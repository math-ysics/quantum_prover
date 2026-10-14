import QuantumProver.InformationTheory.FinitePR.Definitions
import QuantumProver.InformationTheory.FinitePR.Lemmas
import QuantumProver.InformationTheory.FinitePR.ClosedGraphSelector
import QuantumProver.InformationTheory.FinitePR.WeakCouplingDual
import QuantumProver.InformationTheory.FinitePR.CapacityBounds
import QuantumProver.InformationTheory.FinitePR.SphereGeometry
import QuantumProver.InformationTheory.FinitePR.SpherePrior
import QuantumProver.InformationTheory.FinitePR.SquarePartition
import QuantumProver.InformationTheory.FinitePR.SphereRotationTransport
import QuantumProver.InformationTheory.FinitePR.SphereSymmetrization
import QuantumProver.InformationTheory.FinitePR.SamplerIntegralBridge

/-!
Exact finite-alphabet PR simulation of entangled-qubit projective measurements.

The final theorem covers all interior entanglement angles using
the actual sphere prior, measurable finite-list selector and binary PR product.
No project axiom supplies selection, invariance, normalization or simulation.
-/

namespace FinitePR

open scoped BigOperators
open MeasureTheory

theorem prRelation_iff_right (u v α β : Bit) :
    prRelation u v α β ↔ β = u * v - α := by
  simp only [prRelation, eq_sub_iff_add_eq, add_comm α β]

theorem prRelation_iff_left (u v α β : Bit) :
    prRelation u v α β ↔ α = u * v - β := by
  simp only [prRelation, eq_sub_iff_add_eq]

theorem prWeight_nonneg (u v α β : Bit) : 0 ≤ prWeight u v α β := by
  classical
  unfold prWeight
  split_ifs <;> norm_num

/-- Alice's marginal is fair for every pair of PR inputs. -/
theorem prWeight_row_sum (u v α : Bit) :
    ∑ β : Bit, prWeight u v α β = 1 / 2 := by
  classical
  simp only [prWeight, prRelation_iff_right]
  simp

/-- Bob's marginal is fair for every pair of PR inputs. -/
theorem prWeight_column_sum (u v β : Bit) :
    ∑ α : Bit, prWeight u v α β = 1 / 2 := by
  classical
  simp only [prWeight, prRelation_iff_left]
  simp

theorem prWeight_total (u v : Bit) :
    ∑ α : Bit, ∑ β : Bit, prWeight u v α β = 1 := by
  simp [prWeight_row_sum, ZMod.card]

/-- Explicit finite-alphabet nonsignalling of the fixed resource table. -/
theorem prWeight_nonsignalling (u v u' v' α β : Bit) :
    (∑ b : Bit, prWeight u v α b) = (∑ b : Bit, prWeight u v' α b) ∧
    (∑ a : Bit, prWeight u v a β) = (∑ a : Bit, prWeight u' v a β) := by
  simp [prWeight_row_sum, prWeight_column_sum]

/-- The exact product law of exactly `N` independent copies. -/
noncomputable def prVectorWeight {N : ℕ}
    (u v α β : Fin N → Bit) : ℝ := ∏ i, prWeight (u i) (v i) (α i) (β i)

theorem prVectorWeight_row_sum {N : ℕ} (u v α : Fin N → Bit) :
    ∑ β : Fin N → Bit, prVectorWeight u v α β = (1 / 2 : ℝ) ^ N := by
  classical
  unfold prVectorWeight
  rw [← Fintype.prod_sum]
  simp [prWeight_row_sum]

theorem prVectorWeight_column_sum {N : ℕ} (u v β : Fin N → Bit) :
    ∑ α : Fin N → Bit, prVectorWeight u v α β = (1 / 2 : ℝ) ^ N := by
  classical
  unfold prVectorWeight
  rw [← Fintype.prod_sum (fun i a => prWeight (u i) (v i) a (β i))]
  simp [prWeight_column_sum]

theorem prVectorWeight_total {N : ℕ} (u v : Fin N → Bit) :
    ∑ α : Fin N → Bit, ∑ β : Fin N → Bit, prVectorWeight u v α β = 1 := by
  simp only [prVectorWeight_row_sum, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, Fintype.card_fun, Fintype.card_fin, ZMod.card, Nat.cast_pow,
    Nat.cast_ofNat]
  rw [← mul_pow]
  norm_num

/-- A parallel local wiring has no argument carrying the other party's input. -/
structure ParallelPRWiring (X Y Ω : Type*)
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Ω] (N : ℕ) where
  u : X × Ω → Fin N → Bit
  v : Y × Ω → Fin N → Bit
  alice : (X × Ω) × (Fin N → Bit) → Bit
  bob : (Y × Ω) × (Fin N → Bit) → Bit
  measurable_u : Measurable u
  measurable_v : Measurable v
  measurable_alice : Measurable alice
  measurable_bob : Measurable bob

/-- Every measurable finite-index rule and local bit functions produce fixed
jointly measurable local maps. Existence of a rule with the required sampling
law is not assumed or proved by this constructor.
-/
def oneHotWiring {X Y Ω : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Ω] {N : ℕ}
    (I : X × Ω → Fin N) (d : X × Ω → Bit) (e : Y × Ω → Fin N → Bit)
    (hI : Measurable I) (hd : Measurable d) (he : Measurable e) :
    ParallelPRWiring X Y Ω N where
  u z := oneHot (I z)
  v := e
  alice z := aliceParity (d z.1) z.2
  bob z := bobParity z.2
  measurable_u := (measurable_of_finite (fun i : Fin N => oneHot i)).comp hI
  measurable_v := he
  measurable_alice :=
    (measurable_of_finite (fun z : Bit × (Fin N → Bit) => aliceParity z.1 z.2)).comp
      ((hd.comp measurable_fst).prodMk measurable_snd)
  measurable_bob := (measurable_of_finite (fun α : Fin N → Bit => bobParity α)).comp
    measurable_snd

/-- Conditional construction of Bob's PR vector from a fair Alice vector. -/
def prBobVector {N : ℕ} (u v α : Fin N → Bit) : Fin N → Bit :=
  fun i => u i * v i - α i

theorem prBobVector_relation {N : ℕ} (u v α : Fin N → Bit) (i : Fin N) :
    prRelation (u i) (v i) (α i) (prBobVector u v α i) := by
  unfold prRelation prBobVector
  ring

/-- Sampling a uniform Alice vector and its uniquely determined Bob vector
is exactly the product PR law, not an additional communication resource.
-/
theorem prVectorWeight_eq_uniform {N : ℕ} (u v α β : Fin N → Bit) :
    prVectorWeight u v α β =
      if β = prBobVector u v α then
        (Fintype.card (Fin N → Bit) : ℝ)⁻¹ else 0 := by
  classical
  change (∏ i, prWeight (u i) (v i) (α i) (β i)) =
    if β = pairedOutputs u v α then
      (Fintype.card (Fin N → Bit) : ℝ)⁻¹ else 0
  rw [prProduct_graph, bitVector_card]
  simp [one_div]

def protocolOutput {X Y Ω : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Ω] {N : ℕ}
    (W : ParallelPRWiring X Y Ω N) (x : X) (y : Y)
    (z : Ω × (Fin N → Bit)) : Bit × Bit :=
  (W.alice ((x, z.1), z.2),
    W.bob ((y, z.1), prBobVector (W.u (x, z.1)) (W.v (y, z.1)) z.2))

theorem measurable_protocolOutput {X Y Ω : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Ω] {N : ℕ}
    (W : ParallelPRWiring X Y Ω N) (x : X) (y : Y) :
    Measurable (protocolOutput W x y) := by
  have hx : Measurable (fun z : Ω × (Fin N → Bit) => (x, z.1)) :=
    measurable_const.prodMk measurable_fst
  have hy : Measurable (fun z : Ω × (Fin N → Bit) => (y, z.1)) :=
    measurable_const.prodMk measurable_fst
  have hβ : Measurable (fun z : Ω × (Fin N → Bit) =>
      prBobVector (W.u (x, z.1)) (W.v (y, z.1)) z.2) :=
    (measurable_of_finite (fun q :
      (Fin N → Bit) × ((Fin N → Bit) × (Fin N → Bit)) =>
        prBobVector q.1 q.2.1 q.2.2)).comp
      ((W.measurable_u.comp hx).prodMk
        ((W.measurable_v.comp hy).prodMk measurable_snd))
  exact (W.measurable_alice.comp (hx.prodMk measurable_snd)).prodMk
    (W.measurable_bob.comp (hy.prodMk hβ))

/-- Shared randomness has one fixed law, independent of both measurement inputs.
The additional uniform finite vector models the independent PR output masks.
-/
noncomputable def protocolLaw {X Y Ω : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Ω] {N : ℕ}
    (W : ParallelPRWiring X Y Ω N) (μ : Measure Ω) (x : X) (y : Y) :
    Measure (Bit × Bit) :=
  Measure.map (protocolOutput W x y)
    (μ.prod (PMF.uniformOfFintype (Fin N → Bit)).toMeasure)

theorem protocolLaw_probability {X Y Ω : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Ω] {N : ℕ}
    (W : ParallelPRWiring X Y Ω N) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (x : X) (y : Y) : IsProbabilityMeasure (protocolLaw W μ x y) := by
  unfold protocolLaw
  infer_instance

/-- Exact product-measure reduction to a finite conditional PR-output sum. -/
theorem protocolLaw_apply {X Y Ω : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Ω] {N : ℕ}
    (W : ParallelPRWiring X Y Ω N) (μ : Measure Ω) (x : X) (y : Y) (a b : Bit) :
    protocolLaw W μ x y {(a, b)} =
      ∫⁻ ω, ∑ α : Fin N → Bit,
        if protocolOutput W x y (ω, α) = (a, b) then
          (Fintype.card (Fin N → Bit) : ENNReal)⁻¹ else 0 ∂μ := by
  classical
  unfold protocolLaw
  rw [Measure.map_apply (measurable_protocolOutput W x y) (measurableSet_singleton _)]
  rw [Measure.prod_apply
    ((measurable_protocolOutput W x y) (measurableSet_singleton _))]
  apply lintegral_congr
  intro ω
  simp [PMF.toMeasure_apply_fintype, Set.indicator_apply,
    PMF.uniformOfFintype_apply]

/-- The actual local maps have the entire desired conditional pair law. -/
theorem oneHotWiring_joint_mass {X Y Ω : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Ω] {N : ℕ}
    (I : X × Ω → Fin N) (d : X × Ω → Bit) (e : Y × Ω → Fin N → Bit)
    (hI : Measurable I) (hd : Measurable d) (he : Measurable e)
    (x : X) (y : Y) (ω : Ω) (a b : Bit) :
    (∑ α : Fin N → Bit,
      if protocolOutput (oneHotWiring I d e hI hd he) x y (ω, α) = (a, b) then
        1 / (Fintype.card (Fin N → Bit) : ℝ) else 0) =
      if a + b = d (x, ω) + e (y, ω) (I (x, ω)) then 1 / 2 else 0 := by
  have hcard : (Fintype.card (Fin N → Bit) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hprob : (∑ _α : Fin N → Bit,
      1 / (Fintype.card (Fin N → Bit) : ℝ)) = 1 := by simp [hcard]
  have H := oneHot_joint_mass (I (x, ω)) (d (x, ω)) (e (y, ω))
    (prBobVector (oneHot (I (x, ω))) (e (y, ω)))
    (fun _ => 1 / (Fintype.card (Fin N → Bit) : ℝ))
    (fun α i => prBobVector_relation (oneHot (I (x, ω))) (e (y, ω)) α i)
    (fun _ => rfl) hprob a b
  simpa only [protocolOutput, oneHotWiring, Prod.mk.injEq] using H

/-- The concrete Borel shared-data space used by the construction. -/
abbrev SharedSpace (N : ℕ) :=
  (Fin N → Direction) × (ℝ × (Direction × (ℝ × ℝ)))

/-- Exact all-direction simulation with a fixed finite number of the same box.
-/
def HasParallelPRSimulation (θ : ℝ) : Prop :=
  ∃ (N : ℕ) (μ : Measure (SharedSpace N)), IsProbabilityMeasure μ ∧
    ∃ W : ParallelPRWiring Direction Direction (SharedSpace N) N,
      ∀ (x y : Direction) (a b : Bit),
        (protocolLaw W μ x y {(a, b)}).toReal = projectiveProbability θ x y a b

def PartiallyEntangledPRSimulability : Prop :=
  ∀ θ : ℝ, 0 < θ → θ < Real.pi / 4 → HasParallelPRSimulation θ

/-- The conventional Pauli matrices use computational-basis indices `Fin 2`. -/
def pauliX : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

def pauliY : Matrix (Fin 2) (Fin 2) ℂ := !![0, -Complex.I; Complex.I, 0]

def pauliZ : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

noncomputable def pauliObservable (x : Direction) : Matrix (Fin 2) (Fin 2) ℂ :=
  (x.1 0 : ℂ) • pauliX + (x.1 1 : ℂ) • pauliY + (x.1 2 : ℂ) • pauliZ

/-- This is exactly `(I + (-1)^a x·σ)/2`, with a complex scalar. -/
noncomputable def projectiveMatrix (a : Bit) (x : Direction) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  (1 / 2 : ℂ) • (1 + (bitSign a : ℂ) • pauliObservable x)

noncomputable def qubitState (θ : ℝ) (i : Fin 2 × Fin 2) : ℂ :=
  if i = (0, 0) then (Real.cos θ : ℂ)
  else if i = (1, 1) then (Real.sin θ : ℂ) else 0

/-- The exact rank-one density matrix of `cos θ |00⟩ + sin θ |11⟩`. -/
noncomputable def qubitDensity (θ : ℝ) :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  fun i j => qubitState θ i * star (qubitState θ j)

theorem qubitDensity_trace (θ : ℝ) : Matrix.trace (qubitDensity θ) = 1 := by
  apply Complex.ext
  · simp [qubitDensity, qubitState, Matrix.trace, Fintype.sum_prod_type,
      Fin.sum_univ_two, Complex.mul_re, Complex.cos_ofReal_re, Complex.sin_ofReal_re]
    nlinarith [Real.sin_sq_add_cos_sq θ]
  · simp [qubitDensity, qubitState, Matrix.trace, Fintype.sum_prod_type,
      Fin.sum_univ_two, Complex.mul_im]

noncomputable def bornProbability (θ : ℝ) (x y : Direction) (a b : Bit) : ℝ :=
  (Matrix.trace (qubitDensity θ *
    Matrix.kronecker (projectiveMatrix a x) (projectiveMatrix b y))).re

/-- Exact semantic bridge from the original matrix Born rule to the formula.
No measurement-direction or entanglement restriction is used for this identity.
-/
theorem born_eq_projectiveProbability (θ : ℝ) (x y : Direction) (a b : Bit) :
    bornProbability θ x y a b = projectiveProbability θ x y a b := by
  have hs : Real.sin θ ^ 2 = 1 - Real.cos θ ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq θ]
  simp [bornProbability, qubitDensity, qubitState, projectiveMatrix,
    pauliObservable, pauliX, pauliY, pauliZ, Matrix.trace, Matrix.mul_apply,
    Fintype.sum_prod_type, Fin.sum_univ_two,
    Complex.mul_re, Complex.mul_im, projectiveProbability,
    Complex.cos_ofReal_re, Complex.sin_ofReal_re,
    Real.sin_two_mul, Real.cos_two_mul]
  ring_nf
  try simp only [hs]
  ring

theorem born_trace_im (θ : ℝ) (x y : Direction) (a b : Bit) :
    (Matrix.trace (qubitDensity θ *
      Matrix.kronecker (projectiveMatrix a x) (projectiveMatrix b y))).im = 0 := by
  simp [qubitDensity, qubitState, projectiveMatrix, pauliObservable, pauliX,
    pauliY, pauliZ, Matrix.trace, Matrix.mul_apply, Fintype.sum_prod_type,
    Fin.sum_univ_two, Complex.mul_re, Complex.mul_im] <;> ring

/-- Full complex-trace identity, without silently discarding an imaginary part. -/
theorem born_trace_eq_projectiveProbability (θ : ℝ) (x y : Direction) (a b : Bit) :
    Matrix.trace (qubitDensity θ *
      Matrix.kronecker (projectiveMatrix a x) (projectiveMatrix b y)) =
        (projectiveProbability θ x y a b : ℂ) := by
  apply Complex.ext
  · change bornProbability θ x y a b = projectiveProbability θ x y a b
    exact born_eq_projectiveProbability θ x y a b
  · change (Matrix.trace (qubitDensity θ *
      Matrix.kronecker (projectiveMatrix a x) (projectiveMatrix b y))).im = 0
    exact born_trace_im θ x y a b

/-- Exact algebra for the two-element output alphabet. -/
theorem sum_bits (f : Bit → ℝ) : ∑ a : Bit, f a = f 0 + f 1 := by
  classical
  have h : (Finset.univ : Finset Bit) = {0, 1} := by
    ext a
    rcases bit_cases a with rfl | rfl <;> simp
  rw [h]
  simp

/-- The continuum target keeps Alice's actual biased marginal. -/
theorem projectiveProbability_row (θ : ℝ) (x y : Direction) (a : Bit) :
    ∑ b : Bit, projectiveProbability θ x y a b =
      (1 + bitSign a * Real.cos (2 * θ) * x.1 2) / 2 := by
  rw [sum_bits]
  by_cases ha : a = 0 <;> simp [projectiveProbability, bitSign, ha] <;> ring

/-- The continuum target keeps Bob's actual biased marginal. -/
theorem projectiveProbability_column (θ : ℝ) (x y : Direction) (b : Bit) :
    ∑ a : Bit, projectiveProbability θ x y a b =
      (1 + bitSign b * Real.cos (2 * θ) * y.1 2) / 2 := by
  rw [sum_bits]
  by_cases hb : b = 0 <;> simp [projectiveProbability, bitSign, hb] <;> ring

theorem projectiveProbability_total (θ : ℝ) (x y : Direction) :
    ∑ a : Bit, ∑ b : Bit, projectiveProbability θ x y a b = 1 := by
  simp_rw [projectiveProbability_row]
  rw [sum_bits]
  simp [bitSign]
  ring

theorem projectiveProbability_nonsignalling (θ : ℝ) (x y x' y' : Direction)
    (a b : Bit) :
    (∑ c : Bit, projectiveProbability θ x y a c) =
      (∑ c : Bit, projectiveProbability θ x y' a c) ∧
    (∑ c : Bit, projectiveProbability θ x y c b) =
      (∑ c : Bit, projectiveProbability θ x' y c b) := by
  simp [projectiveProbability_row, projectiveProbability_column]

theorem positivePart_formula (t : ℝ) : max t 0 = (t + |t|) / 2 := by
  by_cases ht : 0 ≤ t
  · rw [max_eq_left ht, abs_of_nonneg ht]
    ring
  · have ht' : t ≤ 0 := le_of_not_ge ht
    rw [max_eq_right ht', abs_of_nonpos ht']
    ring

/-- The absolute-value identity behind the exact local/residual decomposition. -/
theorem abs_add_abs_sub_max (u v : ℝ) :
    |u + v| + |u - v| = 2 * max |u| |v| := by
  rcases le_total 0 (u + v) with hp | hp
  · rcases le_total 0 (u - v) with hm | hm
    · have hu : 0 ≤ u := by linarith
      have hv : |v| ≤ u := abs_le.mpr ⟨by linarith, by linarith⟩
      rw [abs_of_nonneg hp, abs_of_nonneg hm, abs_of_nonneg hu, max_eq_left hv]
      ring
    · have hv : 0 ≤ v := by linarith
      have hu : |u| ≤ v := abs_le.mpr ⟨by linarith, by linarith⟩
      rw [abs_of_nonneg hp, abs_of_nonpos hm, abs_of_nonneg hv, max_eq_right hu]
      ring
  · rcases le_total 0 (u - v) with hm | hm
    · have hv : v ≤ 0 := by linarith
      have hu : |u| ≤ -v := abs_le.mpr ⟨by linarith, by linarith⟩
      rw [abs_of_nonpos hp, abs_of_nonneg hm, abs_of_nonpos hv, max_eq_right hu]
      ring
    · have hu : u ≤ 0 := by linarith
      have hv : |v| ≤ -u := abs_le.mpr ⟨by linarith, by linarith⟩
      rw [abs_of_nonpos hp, abs_of_nonpos hm, abs_of_nonpos hu, max_eq_left hv]
      ring

theorem residual_positivePart_core (u v : ℝ) :
    max ((u + v) / 2) 0 + max ((u - v) / 2) 0 - max u 0 =
      max (|v| - |u|) 0 / 2 := by
  rw [positivePart_formula ((u + v) / 2), positivePart_formula ((u - v) / 2),
    positivePart_formula u]
  norm_num only [abs_div]
  have h := abs_add_abs_sub_max u v
  by_cases hle : |u| ≤ |v|
  · rw [max_eq_right hle] at h
    rw [max_eq_left (sub_nonneg.mpr hle)]
    linarith
  · have hge : |v| ≤ |u| := le_of_not_ge hle
    rw [max_eq_left hge] at h
    rw [max_eq_right (sub_nonpos.mpr hge)]
    linarith

theorem positivePart_scale (c t : ℝ) (hc : 0 ≤ c) :
    max (c * t) 0 = c * max t 0 := by
  by_cases ht : 0 ≤ t
  · rw [max_eq_left ht, max_eq_left (mul_nonneg hc ht)]
  · have ht' : t ≤ 0 := le_of_not_ge ht
    rw [max_eq_right ht', max_eq_right (mul_nonpos_of_nonneg_of_nonpos hc ht')]
    simp

/-- This proves the residual numerator exactly, including every zero. -/
theorem residual_positivePart (c t w : ℝ) (hc : 0 ≤ c) :
    max ((c * t + w) / 2) 0 + max ((c * t - w) / 2) 0 - c * max t 0 =
      max (|w| - c * |t|) 0 / 2 := by
  rw [← positivePart_scale c t hc, residual_positivePart_core]
  simp [abs_mul, abs_of_nonneg hc]

theorem residual_numerator_nonneg (c t w : ℝ) (hc : 0 ≤ c) :
    0 ≤ max ((c * t + w) / 2) 0 + max ((c * t - w) / 2) 0 - c * max t 0 := by
  rw [residual_positivePart c t w hc]
  positivity

end FinitePR

/-!
Actual compactness and convexity of supported probability couplings.
These results do not assert that an arbitrary prescribed second marginal is
attainable. The capacity sufficiency and Borel parameter selector remain open.
-/

namespace FinitePR.Coupling

open MeasureTheory Set
open scoped NNReal ENNReal

variable {L S : Type*} [MeasurableSpace L] [MeasurableSpace S]

/-- The mass-one finite measures with a fixed first marginal, supported on F. -/
def supportedCouplings (K : ProbabilityMeasure L) (F : Set (L × S)) :
    Set (FiniteMeasure (L × S)) :=
  {π | π.mass = 1 ∧ π.map Prod.fst = K.toFiniteMeasure ∧ π Fᶜ = 0}

/-- The identical coupling family represented by actual probability measures. -/
def probabilityCouplings (K : ProbabilityMeasure L) (F : Set (L × S)) :
    Set (ProbabilityMeasure (L × S)) :=
  {π | π.toFiniteMeasure ∈ supportedCouplings K F}

/-- The attainable second marginals, in the finite-measure linear cone. -/
def marginalImage (K : ProbabilityMeasure L) (F : Set (L × S)) :
    Set (FiniteMeasure S) :=
  (fun π : FiniteMeasure (L × S) => π.map Prod.snd) '' supportedCouplings K F

/-- The same second-marginal image represented by actual probability measures. -/
def probabilityMarginalImage (K : ProbabilityMeasure L) (F : Set (L × S)) :
    Set (ProbabilityMeasure S) :=
  (fun π : ProbabilityMeasure (L × S) => π.map Prod.snd) '' probabilityCouplings K F

theorem supportedCouplings_convex (K : ProbabilityMeasure L) (F : Set (L × S)) :
    Convex ℝ≥0 (supportedCouplings K F) := by
  intro π hπ ρ hρ a b _ha _hb hab
  refine ⟨?_, ?_, ?_⟩
  · simp only [FiniteMeasure.mass, FiniteMeasure.coeFn_add, Pi.add_apply,
      FiniteMeasure.smul_apply, smul_eq_mul]
    change a * π.mass + b * ρ.mass = 1
    rw [hπ.1, hρ.1, mul_one, mul_one, hab]
  · rw [FiniteMeasure.map_add measurable_fst,
      FiniteMeasure.map_smul a measurable_fst.aemeasurable,
      FiniteMeasure.map_smul b measurable_fst.aemeasurable,
      hπ.2.1, hρ.2.1, ← add_smul, hab, one_smul]
  · simp [FiniteMeasure.coeFn_add, Pi.add_apply, FiniteMeasure.smul_apply,
      hπ.2.2, hρ.2.2]

theorem toFiniteMeasure_image_probabilityCouplings
    (K : ProbabilityMeasure L) (F : Set (L × S)) :
    ProbabilityMeasure.toFiniteMeasure '' probabilityCouplings K F =
      supportedCouplings K F := by
  ext π
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact hq
  · intro hπ
    have hrange : π ∈ Set.range
        (ProbabilityMeasure.toFiniteMeasure : ProbabilityMeasure (L × S) → _) := by
      rw [ProbabilityMeasure.range_toFiniteMeasure]
      exact hπ.1
    obtain ⟨q, hq⟩ := hrange
    exact ⟨q, by simpa only [probabilityCouplings, Set.mem_setOf_eq, hq] using hπ, hq⟩

variable [MetricSpace L] [MetricSpace S] [CompactSpace L] [CompactSpace S]
    [BorelSpace L] [BorelSpace S]

/-- Prokhorov compactness restricted to mass one and a fixed first marginal. -/
theorem supportedCouplings_isCompact (K : ProbabilityMeasure L)
    {F : Set (L × S)} (hF : IsClosed F) : IsCompact (supportedCouplings K F) := by
  have hc : IsCompact {π : FiniteMeasure (L × S) | π.mass ≤ 1 ∧ π Fᶜ = 0} :=
    isCompact_setOfPred_finiteMeasure_le_of_isCompact 1 hF.isCompact
  have hm : IsClosed {π : FiniteMeasure (L × S) | π.mass = 1} :=
    isClosed_eq FiniteMeasure.continuous_mass continuous_const
  have hk : IsClosed {π : FiniteMeasure (L × S) | π.map Prod.fst = K.toFiniteMeasure} :=
    isClosed_eq (FiniteMeasure.continuous_map continuous_fst) continuous_const
  have heq : supportedCouplings K F =
      {π : FiniteMeasure (L × S) | π.mass ≤ 1 ∧ π Fᶜ = 0} ∩
        {π | π.mass = 1} ∩ {π | π.map Prod.fst = K.toFiniteMeasure} := by
    ext π
    simp only [supportedCouplings, Set.mem_setOf_eq, Set.mem_inter_iff]
    constructor
    · intro h
      exact ⟨⟨⟨le_of_eq h.1, h.2.2⟩, h.1⟩, h.2.1⟩
    · intro h
      exact ⟨h.1.2, h.2, h.1.1.2⟩
  rw [heq]
  exact (hc.inter_right hm).inter_right hk

theorem probabilityCouplings_isCompact (K : ProbabilityMeasure L)
    {F : Set (L × S)} (hF : IsClosed F) : IsCompact (probabilityCouplings K F) := by
  apply (ProbabilityMeasure.toFiniteMeasure_isEmbedding (L × S)).isCompact_iff.2
  rw [toFiniteMeasure_image_probabilityCouplings]
  exact supportedCouplings_isCompact K hF

theorem probabilityCouplings_isClosed (K : ProbabilityMeasure L)
    {F : Set (L × S)} (hF : IsClosed F) : IsClosed (probabilityCouplings K F) :=
  (probabilityCouplings_isCompact K hF).isClosed

/-- The support condition is the literal probability-one incidence condition. -/
theorem mem_probabilityCouplings_iff (K : ProbabilityMeasure L)
    {F : Set (L × S)} (hF : IsClosed F) (π : ProbabilityMeasure (L × S)) :
    π ∈ probabilityCouplings K F ↔
      (π : Measure (L × S)).map Prod.fst = (K : Measure L) ∧
        (π : Measure (L × S)) F = 1 := by
  constructor
  · intro hπ
    refine ⟨?_, ?_⟩
    · simpa only [FiniteMeasure.toMeasure_map,
        ProbabilityMeasure.toMeasure_comp_toFiniteMeasure_eq_toMeasure] using
        congrArg FiniteMeasure.toMeasure hπ.2.1
    · have hzero : (π : Measure (L × S)) Fᶜ = 0 :=
        (FiniteMeasure.null_iff_toMeasure_null π.toFiniteMeasure Fᶜ).mp hπ.2.2
      have hsum := measure_add_measure_compl (μ := (π : Measure (L × S))) hF.measurableSet
      simpa only [hzero, add_zero, measure_univ] using hsum
  · intro hπ
    refine ⟨ProbabilityMeasure.mass_toFiniteMeasure π, ?_, ?_⟩
    · apply FiniteMeasure.toMeasure_injective
      simpa only [FiniteMeasure.toMeasure_map,
        ProbabilityMeasure.toMeasure_comp_toFiniteMeasure_eq_toMeasure] using hπ.1
    · apply (FiniteMeasure.null_iff_toMeasure_null π.toFiniteMeasure Fᶜ).mpr
      rw [ProbabilityMeasure.toMeasure_comp_toFiniteMeasure_eq_toMeasure,
        measure_compl hF.measurableSet (measure_ne_top _ _), measure_univ, hπ.2]
      simp

theorem marginalImage_isCompact (K : ProbabilityMeasure L)
    {F : Set (L × S)} (hF : IsClosed F) : IsCompact (marginalImage K F) :=
  (supportedCouplings_isCompact K hF).image
    (FiniteMeasure.continuous_map continuous_snd)

theorem marginalImage_convex (K : ProbabilityMeasure L) (F : Set (L × S)) :
    Convex ℝ≥0 (marginalImage K F) :=
  (supportedCouplings_convex K F).linear_image (FiniteMeasure.mapHom measurable_snd)

theorem marginalImage_isClosed (K : ProbabilityMeasure L)
    {F : Set (L × S)} (hF : IsClosed F) : IsClosed (marginalImage K F) :=
  (marginalImage_isCompact K hF).isClosed

theorem probabilityMarginalImage_isCompact (K : ProbabilityMeasure L)
    {F : Set (L × S)} (hF : IsClosed F) : IsCompact (probabilityMarginalImage K F) :=
  (probabilityCouplings_isCompact K hF).image
    (ProbabilityMeasure.continuous_map continuous_snd)

theorem secondMarginal_mix (π ρ : FiniteMeasure (L × S)) (a b : ℝ≥0) :
    (a • π + b • ρ).map Prod.snd = a • π.map Prod.snd + b • ρ.map Prod.snd := by
  rw [FiniteMeasure.map_add measurable_snd,
    FiniteMeasure.map_smul a measurable_snd.aemeasurable,
    FiniteMeasure.map_smul b measurable_snd.aemeasurable]

end FinitePR.Coupling

namespace FinitePR.Sampling

open MeasureTheory Set
open scoped ENNReal

variable {S : Type*} [MetricSpace S] [MeasurableSpace S] [BorelSpace S]
  [CompactSpace S]

/-- The prescribed law is the actual normalized continuous density against q. -/
noncomputable def densityProbability (q : ProbabilityMeasure S) (f : S → ℝ)
    (hf : Continuous f) (hnonneg : ∀ z, 0 ≤ f z)
    (hnormalized : ∫ z, f z ∂(q : Measure S) = 1) : ProbabilityMeasure S := by
  have hfi : Integrable f (q : Measure S) :=
    hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)
  refine ⟨(q : Measure S).withDensity (fun z => ENNReal.ofReal (f z)), ⟨?_⟩⟩
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hfi (ae_of_all _ hnonneg), hnormalized]
  norm_num

theorem densityProbability_apply (q : ProbabilityMeasure S) (f : S → ℝ)
    (hf : Continuous f) (hnonneg : ∀ z, 0 ≤ f z)
    (hnormalized : ∫ z, f z ∂(q : Measure S) = 1)
    {B : Set S} (hB : MeasurableSet B) :
    (densityProbability q f hf hnonneg hnormalized : Measure S) B =
      ENNReal.ofReal (∫ z in B, f z ∂(q : Measure S)) := by
  have hfi : Integrable f (q : Measure S) :=
    hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)
  change ((q : Measure S).withDensity (fun z => ENNReal.ofReal (f z))) B = _
  rw [withDensity_apply _ hB]
  exact (ofReal_integral_eq_lintegral_ofReal hfi.integrableOn
    (ae_of_all _ hnonneg)).symm

theorem densityProbability_integral (q : ProbabilityMeasure S) (f : S → ℝ)
    (hf : Continuous f) (hnonneg : ∀ z, 0 ≤ f z)
    (hnormalized : ∫ z, f z ∂(q : Measure S) = 1) (g : S → ℝ) :
    (∫ z, g z ∂(densityProbability q f hf hnonneg hnormalized : Measure S)) =
      ∫ z, f z * g z ∂(q : Measure S) := by
  change (∫ z, g z ∂(q : Measure S).withDensity (fun z => ENNReal.ofReal (f z))) = _
  rw [integral_withDensity_eq_integral_toReal_smul hf.measurable.ennreal_ofReal
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (hnonneg _), smul_eq_mul]

variable {X : Type*} [MetricSpace X] [CompactSpace X]

noncomputable def densityFamily (q : ProbabilityMeasure S) (f : X × S → ℝ)
    (hf : Continuous f) (hnonneg : ∀ x z, 0 ≤ f (x, z))
    (hnormalized : ∀ x, ∫ z, f (x, z) ∂(q : Measure S) = 1) :
    X → ProbabilityMeasure S := fun x =>
  densityProbability q (fun z => f (x, z))
    (hf.comp (continuous_const.prodMk continuous_id)) (hnonneg x) (hnormalized x)

/-- Joint continuity on compact spaces gives weak continuity of the actual density laws. -/
theorem densityFamily_continuous (q : ProbabilityMeasure S) (f : X × S → ℝ)
    (hf : Continuous f) (hnonneg : ∀ x z, 0 ≤ f (x, z))
    (hnormalized : ∀ x, ∫ z, f (x, z) ∂(q : Measure S) = 1) :
    Continuous (densityFamily q f hf hnonneg hnormalized) := by
  apply ProbabilityMeasure.continuous_iff_forall_continuousMap_continuous_integral.mpr
  intro g
  have hc : Continuous (fun x =>
      ∫ z in (univ : Set S), f (x, z) * g z ∂(q : Measure S)) :=
    continuous_parametric_integral_of_continuous
      (hf.mul (g.continuous.comp continuous_snd)) isCompact_univ
  simpa only [densityFamily, densityProbability_integral, Measure.restrict_univ] using hc

end FinitePR.Sampling

/-!
The actual unit sphere and finite-list incidence relation.  Coordinate selection
proves the fixed-first-marginal coupling family is nonempty; it does not impose
a specified second marginal.  The final selector theorem keeps attainability of
every prescribed marginal as an explicit predecessor obligation.
-/

namespace FinitePR

open MeasureTheory Set
open scoped BigOperators

theorem directionSet_isClosed :
    IsClosed {x : Fin 3 → ℝ | ∑ i, (x i) ^ 2 = 1} := by
  exact isClosed_eq (continuous_finset_sum _ (fun i _ =>
    (continuous_apply i).pow 2)) continuous_const

theorem directionSet_isCompact :
    IsCompact {x : Fin 3 → ℝ | ∑ i, (x i) ^ 2 = 1} := by
  refine Metric.isCompact_iff_isClosed_bounded.mpr ⟨directionSet_isClosed, ?_⟩
  refine isBounded_iff_forall_norm_le.mpr ⟨1, ?_⟩
  intro x hx
  apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
  intro i
  have hi : (x i) ^ 2 ≤ 1 := by
    calc
      (x i) ^ 2 ≤ ∑ j, (x j) ^ 2 :=
        Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
      _ = 1 := hx
  rw [Real.norm_eq_abs]
  exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩

instance directionCompactSpace : CompactSpace Direction :=
  isCompact_iff_compactSpace.mp directionSet_isCompact

instance directionNonempty : Nonempty Direction := by
  refine ⟨⟨![0, 0, 1], ?_⟩⟩
  norm_num [Fin.sum_univ_succ]

end FinitePR

namespace FinitePR.Coupling

open MeasureTheory Set

variable {S : Type*} [MetricSpace S] [MeasurableSpace S] [BorelSpace S]
  [CompactSpace S]

/-- The selected point is literally one of the finite list coordinates. -/
def listIncidence (N : ℕ) : Set ((Fin N → S) × S) :=
  {p | ∃ i : Fin N, p.2 = p.1 i}

theorem listIncidence_isClosed (N : ℕ) : IsClosed (listIncidence (S := S) N) := by
  have heq : listIncidence (S := S) N =
      ⋃ i : Fin N, {p : (Fin N → S) × S | p.2 = p.1 i} := by
    ext p
    simp [listIncidence]
  rw [heq]
  exact isClosed_iUnion_of_finite (fun i =>
    isClosed_eq continuous_snd ((continuous_apply i).comp continuous_fst))

theorem listIncidence_isCompact (N : ℕ) : IsCompact (listIncidence (S := S) N) :=
  (listIncidence_isClosed N).isCompact

/-- A coordinate graph yields a real supported coupling with first marginal K. -/
theorem coordinateCoupling_mem {N : ℕ} (K : ProbabilityMeasure (Fin N → S))
    (i : Fin N) :
    K.map (fun z => (z, z i)) ∈ probabilityCouplings K (listIncidence N) := by
  have hf : Measurable (fun z : Fin N → S => (z, z i)) :=
    (continuous_id.prodMk (continuous_apply i)).measurable
  apply (mem_probabilityCouplings_iff K (listIncidence_isClosed N) _).mpr
  refine ⟨?_, ?_⟩
  · rw [ProbabilityMeasure.toMeasure_map, Measure.map_map measurable_fst hf]
    change Measure.map id (K : Measure (Fin N → S)) = (K : Measure (Fin N → S))
    exact Measure.map_id
  · rw [ProbabilityMeasure.map_apply' K hf.aemeasurable
      (listIncidence_isClosed N).measurableSet]
    have hp : (fun z : Fin N → S => (z, z i)) ⁻¹' listIncidence N = univ := by
      ext z
      simp only [mem_preimage, listIncidence, mem_setOf_eq, mem_univ, iff_true]
      exact ⟨i, rfl⟩
    rw [hp, measure_univ]

theorem probabilityCouplings_list_nonempty {N : ℕ}
    (K : ProbabilityMeasure (Fin N → S)) (hN : 0 < N) :
    (probabilityCouplings K (listIncidence N)).Nonempty :=
  ⟨K.map (fun z => (z, z ⟨0, hN⟩)), coordinateCoupling_mem K ⟨0, hN⟩⟩

theorem sphereList_probabilityCouplings_isCompact (N : ℕ)
    (K : ProbabilityMeasure (Fin N → Direction)) :
    IsCompact (probabilityCouplings K (listIncidence N)) :=
  probabilityCouplings_isCompact K (listIncidence_isClosed N)

theorem sphereList_marginalImage_isCompact (N : ℕ)
    (K : ProbabilityMeasure (Fin N → Direction)) :
    IsCompact (marginalImage K (listIncidence N)) :=
  marginalImage_isCompact K (listIncidence_isClosed N)

end FinitePR.Coupling

namespace FinitePR.Coupling

open MeasureTheory Set

variable {X L S : Type*} [TopologicalSpace X]
  [MetricSpace L] [MetricSpace S] [CompactSpace L] [CompactSpace S]
  [MeasurableSpace L] [MeasurableSpace S] [BorelSpace L] [BorelSpace S]

/-- The exact graph for fixed first marginal, closed support, and moving second marginal. -/
def couplingGraph (K : ProbabilityMeasure L) (F : Set (L × S))
    (ν : X → ProbabilityMeasure S) : Set (X × ProbabilityMeasure (L × S)) :=
  {p | p.2 ∈ probabilityCouplings K F ∧ p.2.map Prod.snd = ν p.1}

theorem couplingGraph_isClosed (K : ProbabilityMeasure L)
    {F : Set (L × S)} (hF : IsClosed F)
    {ν : X → ProbabilityMeasure S} (hν : Continuous ν) :
    IsClosed (couplingGraph K F ν) :=
  ((probabilityCouplings_isClosed K hF).preimage continuous_snd).inter
    (isClosed_eq ((ProbabilityMeasure.continuous_map continuous_snd).comp continuous_snd)
      (hν.comp continuous_fst))

theorem couplingGraph_isCompact [CompactSpace X] (K : ProbabilityMeasure L)
    {F : Set (L × S)} (hF : IsClosed F)
    {ν : X → ProbabilityMeasure S} (hν : Continuous ν) :
    IsCompact (couplingGraph K F ν) := (couplingGraph_isClosed K hF hν).isCompact

/-- Weak-topology Borel choice of attained marginals, with exact coupling constraints.
The hypothesis `hνmem` states that the prescribed marginal belongs to the attainable set.
-/
theorem exists_borel_coupling_selector [MeasurableSpace X] [OpensMeasurableSpace X]
    (K : ProbabilityMeasure L) {F : Set (L × S)} (hF : IsClosed F)
    (hne : (probabilityCouplings K F).Nonempty)
    {ν : X → ProbabilityMeasure S} (hν : Continuous ν)
    (hνmem : ∀ x, ν x ∈ probabilityMarginalImage K F) :
    ∃ s : X → ProbabilityMeasure (L × S),
      @Measurable X (ProbabilityMeasure (L × S)) _
        (borel (ProbabilityMeasure (L × S))) s ∧
      ∀ x, (x, s x) ∈ couplingGraph K F ν := by
  letI : MeasurableSpace (ProbabilityMeasure (L × S)) :=
    borel (ProbabilityMeasure (L × S))
  letI : BorelSpace (ProbabilityMeasure (L × S)) := ⟨rfl⟩
  let Q := probabilityCouplings K F
  letI : CompactSpace Q := isCompact_iff_compactSpace.mp
    (probabilityCouplings_isCompact K hF)
  letI : Nonempty Q := hne.to_subtype
  letI : MeasurableSpace Q := borel Q
  letI : BorelSpace Q := ⟨rfl⟩
  let G : Set (X × Q) := {p | p.2.1.map Prod.snd = ν p.1}
  have hG : IsClosed G :=
    isClosed_eq
      ((ProbabilityMeasure.continuous_map continuous_snd).comp
        (continuous_subtype_val.comp continuous_snd))
      (hν.comp continuous_fst)
  have hGne : ∀ x, ∃ q, (x, q) ∈ G := by
    intro x
    obtain ⟨π, hπ, hmap⟩ := hνmem x
    exact ⟨⟨π, hπ⟩, hmap⟩
  obtain ⟨s, hs, hsmem⟩ :=
    FinitePR.Selection.exists_measurable_selector_of_metrizable G hG hGne
  refine ⟨fun x => (s x).1, ?_, ?_⟩
  · exact (continuous_subtype_val.measurable :
      @Measurable Q (ProbabilityMeasure (L × S)) _
        (borel (ProbabilityMeasure (L × S))) Subtype.val).comp hs
  · intro x
    exact ⟨(s x).2, hsmem x⟩

end FinitePR.Coupling

namespace FinitePR.Coupling

open MeasureTheory Set Filter
open scoped Topology

variable {S : Type*} [MetricSpace S] [MeasurableSpace S] [BorelSpace S]

/-- Borel probability evaluation in the weak topology is Giry measurable. -/
theorem measurable_probability_toMeasure_of_borel :
    @Measurable (ProbabilityMeasure S) (Measure S)
      (borel (ProbabilityMeasure S)) _ ProbabilityMeasure.toMeasure := by
  letI : MeasurableSpace (ProbabilityMeasure S) := borel (ProbabilityMeasure S)
  letI : BorelSpace (ProbabilityMeasure S) := ⟨rfl⟩
  apply Measurable.measure_of_isPiSystem_of_isProbabilityMeasure
    (μ := ProbabilityMeasure.toMeasure) BorelSpace.measurable_eq isPiSystem_isOpen
  intro U hU
  have hsemi : LowerSemicontinuous (fun π : ProbabilityMeasure S => π.toMeasure U) :=
    lowerSemicontinuous_iff_le_liminf.mpr (fun π =>
      ProbabilityMeasure.le_liminf_measure_open_of_tendsto tendsto_id hU)
  exact hsemi.measurable

end FinitePR.Coupling

namespace FinitePR.Coupling

open MeasureTheory Set
open scoped BigOperators ENNReal BoundedContinuousFunction

variable {L S : Type*} [MetricSpace L] [MetricSpace S]
  [MeasurableSpace L] [MeasurableSpace S] [BorelSpace L] [BorelSpace S]
  [CompactSpace L] [CompactSpace S]

/-- A measurable graph through the support relation gives an actual coupling. -/
theorem graphCoupling_mem (K : ProbabilityMeasure L) {F : Set (L × S)}
    (hF : IsClosed F) (s : L → S) (hs : Measurable s)
    (hsmem : ∀ z, (z, s z) ∈ F) :
    K.map (fun z => (z, s z)) ∈ probabilityCouplings K F := by
  have hg : Measurable (fun z : L => (z, s z)) := measurable_id.prodMk hs
  apply (mem_probabilityCouplings_iff K hF _).mpr
  refine ⟨?_, ?_⟩
  · rw [ProbabilityMeasure.toMeasure_map, Measure.map_map measurable_fst hg]
    change Measure.map id (K : Measure L) = (K : Measure L)
    exact Measure.map_id
  · rw [ProbabilityMeasure.map_apply' K hg.aemeasurable hF.measurableSet]
    have hp : (fun z => (z, s z)) ⁻¹' F = univ :=
      Set.eq_univ_of_forall hsmem
    rw [hp, measure_univ]

end FinitePR.Coupling

namespace FinitePR.Coupling

open MeasureTheory Set
open scoped BigOperators ENNReal BoundedContinuousFunction

variable {S : Type*} [MetricSpace S] [MeasurableSpace S] [BorelSpace S]
  [CompactSpace S] {N : ℕ}

private theorem listUnivNonempty (hN : 0 < N) :
    (Finset.univ : Finset (Fin N)).Nonempty := ⟨⟨0, hN⟩, Finset.mem_univ _⟩

/-- The actual largest value of a real test function on a nonempty finite list. -/
noncomputable def listMaximum (hN : 0 < N) (f : S → ℝ) (z : Fin N → S) : ℝ :=
  Finset.univ.sup' (listUnivNonempty hN) (fun i => f (z i))

theorem listMaximum_continuous (hN : 0 < N) {f : S → ℝ} (hf : Continuous f) :
    Continuous (listMaximum hN f) :=
  Continuous.finset_sup'_apply _ (fun i _ => hf.comp (continuous_apply i))

theorem le_listMaximum (hN : 0 < N) (f : S → ℝ) (z : Fin N → S) (i : Fin N) :
    f (z i) ≤ listMaximum hN f z :=
  Finset.le_sup' (fun j => f (z j)) (Finset.mem_univ i)

theorem lt_listMaximum_iff (hN : 0 < N) (f : S → ℝ) (z : Fin N → S) (t : ℝ) :
    t < listMaximum hN f z ↔ ∃ i : Fin N, t < f (z i) := by
  unfold listMaximum
  rw [Finset.lt_sup'_iff]
  simp only [Finset.mem_univ, true_and]

theorem listMaximum_add_const (hN : 0 < N) (f : S → ℝ)
    (z : Fin N → S) (b : ℝ) :
    listMaximum hN (fun t => f t + b) z = listMaximum hN f z + b := by
  exact (Finset.sup'_add Finset.univ (fun i => f (z i)) b _).symm

/-- A single Borel point selection attaining the finite-list maximum. -/
theorem exists_measurable_maximizing_selector [Nonempty S] (hN : 0 < N)
    (f : S →ᵇ ℝ) :
    ∃ s : (Fin N → S) → S, Measurable s ∧
      ∀ z, (z, s z) ∈ listIncidence N ∧ f (s z) = listMaximum hN f z := by
  let G : Set ((Fin N → S) × S) :=
    {p | p ∈ listIncidence N ∧ f p.2 = listMaximum hN f p.1}
  have hG : IsClosed G := (listIncidence_isClosed N).inter
    (isClosed_eq (f.continuous.comp continuous_snd)
      ((listMaximum_continuous hN f.continuous).comp continuous_fst))
  have hne : ∀ z, ∃ t, (z, t) ∈ G := by
    intro z
    obtain ⟨i, _hi, hmax⟩ := Finset.exists_mem_eq_sup'
      (s := (Finset.univ : Finset (Fin N))) ⟨⟨0, hN⟩, Finset.mem_univ _⟩
      (fun i => f (z i))
    exact ⟨z i, ⟨⟨i, rfl⟩, hmax.symm⟩⟩
  exact FinitePR.Selection.exists_measurable_selector G hG hne

/-- The maximal-test second marginal is attained by a genuine supported coupling. -/
theorem exists_maximizing_marginal [Nonempty S] (hN : 0 < N)
    (K : ProbabilityMeasure (Fin N → S)) (f : S →ᵇ ℝ) :
    ∃ η ∈ marginalImage K (listIncidence N),
      (∫ t, f t ∂(η : Measure S)) = ∫ z, listMaximum hN f z ∂(K : Measure _) := by
  obtain ⟨s, hs, hsmem⟩ := exists_measurable_maximizing_selector hN f
  let π := K.map (fun z => (z, s z))
  have hπ : π ∈ probabilityCouplings K (listIncidence N) :=
    graphCoupling_mem K (listIncidence_isClosed N) s hs (fun z => (hsmem z).1)
  have hg : Measurable (fun z : Fin N → S => (z, s z)) := measurable_id.prodMk hs
  refine ⟨π.toFiniteMeasure.map Prod.snd, ⟨π.toFiniteMeasure, hπ, rfl⟩, ?_⟩
  rw [FiniteMeasure.toMeasure_map,
    ProbabilityMeasure.toMeasure_comp_toFiniteMeasure_eq_toMeasure,
    ProbabilityMeasure.toMeasure_map,
    Measure.map_map measurable_snd hg]
  change (∫ t, f t ∂Measure.map s (K : Measure _)) = _
  rw [integral_map hs.aemeasurable f.continuous.measurable.aestronglyMeasurable]
  exact integral_congr_ae (Filter.Eventually.of_forall (fun z => (hsmem z).2))

/- All-set hitting domination becomes real-test domination by layer cake. -/
theorem integral_le_listMaximum_of_capacity (hN : 0 < N)
    (K : ProbabilityMeasure (Fin N → S)) (ν : ProbabilityMeasure S)
    (hcap : ∀ B : Set S, MeasurableSet B →
      (ν : Measure S) B ≤ (K : Measure (Fin N → S)) {z | ∃ i : Fin N, z i ∈ B})
    (f : S →ᵇ ℝ) :
    (∫ t, f t ∂(ν : Measure S)) ≤
      ∫ z, listMaximum hN f z ∂(K : Measure _) := by
  let g : S →ᵇ ℝ := f + BoundedContinuousFunction.const S ‖f‖
  have hgnn : ∀ t, 0 ≤ g t := by
    intro t
    have h := f.norm_coe_le_norm t
    rw [Real.norm_eq_abs] at h
    have hlow := (abs_le.mp h).1
    change 0 ≤ f t + ‖f‖
    linarith
  let m : (Fin N → S) →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact
    ⟨listMaximum hN g, listMaximum_continuous hN g.continuous⟩
  have hmnn : ∀ z, 0 ≤ m z := fun z =>
    (hgnn (z ⟨0, hN⟩)).trans (le_listMaximum hN g z ⟨0, hN⟩)
  have hlayer : (∫⁻ t, ENNReal.ofReal (g t) ∂(ν : Measure S)) ≤
      ∫⁻ z, ENNReal.ofReal (m z) ∂(K : Measure _) := by
    rw [lintegral_eq_lintegral_meas_lt _ (Filter.Eventually.of_forall hgnn)
        g.continuous.measurable.aemeasurable,
      lintegral_eq_lintegral_meas_lt _ (Filter.Eventually.of_forall hmnn)
        m.continuous.measurable.aemeasurable]
    apply lintegral_mono
    intro t
    have h := hcap {a | t < g a}
      (isOpen_lt continuous_const g.continuous).measurableSet
    have heq : {z : Fin N → S | ∃ i : Fin N, z i ∈ {a | t < g a}} =
        {z | t < m z} := by
      ext z
      exact (lt_listMaximum_iff hN g z t).symm
    rwa [heq] at h
  have hreal := ENNReal.toReal_mono
    (m.lintegral_of_real_lt_top (K : Measure _)).ne hlayer
  have eg : (∫ t, g t ∂(ν : Measure S)) =
      (∫⁻ t, ENNReal.ofReal (g t) ∂(ν : Measure S)).toReal :=
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hgnn)
      g.continuous.measurable.aestronglyMeasurable
  have em : (∫ z, m z ∂(K : Measure _)) =
      (∫⁻ z, ENNReal.ofReal (m z) ∂(K : Measure _)).toReal :=
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hmnn)
      m.continuous.measurable.aestronglyMeasurable
  rw [← eg, ← em] at hreal
  have egshift : (∫ t, g t ∂(ν : Measure S)) =
      (∫ t, f t ∂(ν : Measure S)) + ‖f‖ := by
    change (∫ t, f t + ‖f‖ ∂(ν : Measure S)) = _
    rw [integral_add (f.integrable _) (integrable_const _)]
    simp
  have emshift : (∫ z, m z ∂(K : Measure _)) =
      (∫ z, listMaximum hN f z ∂(K : Measure _)) + ‖f‖ := by
    have hem : ∀ z, m z = listMaximum hN f z + ‖f‖ := fun z =>
      listMaximum_add_const hN f z ‖f‖
    have hmi : Integrable (listMaximum hN f) (K : Measure _) :=
      (BoundedContinuousFunction.mkOfCompact
        ⟨listMaximum hN f, listMaximum_continuous hN f.continuous⟩).integrable _
    calc
      (∫ z, m z ∂(K : Measure _)) =
          ∫ z, listMaximum hN f z + ‖f‖ ∂(K : Measure _) :=
        integral_congr_ae (Filter.Eventually.of_forall hem)
      _ = (∫ z, listMaximum hN f z ∂(K : Measure _)) + ‖f‖ := by
        rw [integral_add hmi (integrable_const _)]
        simp
  rw [egshift, emshift] at hreal
  linarith

end FinitePR.Coupling

namespace FinitePR.Coupling

open MeasureTheory Set

variable {X L S : Type*} [TopologicalSpace X]
  [MetricSpace L] [MetricSpace S] [CompactSpace L] [CompactSpace S]
  [MeasurableSpace L] [MeasurableSpace S] [BorelSpace L] [BorelSpace S]

theorem toFiniteMeasure_image_probabilityMarginalImage
    (K : ProbabilityMeasure L) (F : Set (L × S)) :
    ProbabilityMeasure.toFiniteMeasure '' probabilityMarginalImage K F =
      marginalImage K F := by
  have hmap (π : ProbabilityMeasure (L × S)) :
      (π.map Prod.snd).toFiniteMeasure = π.toFiniteMeasure.map Prod.snd := by
    apply FiniteMeasure.toMeasure_injective
    simp only [FiniteMeasure.toMeasure_map, ProbabilityMeasure.toMeasure_map,
      ProbabilityMeasure.toMeasure_comp_toFiniteMeasure_eq_toMeasure]
  ext η
  constructor
  · rintro ⟨q, ⟨π, hπ, rfl⟩, rfl⟩
    exact ⟨π.toFiniteMeasure, hπ, (hmap π).symm⟩
  · rintro ⟨π, hπ, hη⟩
    obtain ⟨q, hq, hqπ⟩ :=
      (toFiniteMeasure_image_probabilityCouplings K F).symm ▸ hπ
    refine ⟨q.map Prod.snd, ⟨q, hq, rfl⟩, ?_⟩
    rw [hmap, hqπ]
    exact hη

theorem mem_probabilityMarginalImage_iff (K : ProbabilityMeasure L)
    (F : Set (L × S)) (ν : ProbabilityMeasure S) :
    ν ∈ probabilityMarginalImage K F ↔ ν.toFiniteMeasure ∈ marginalImage K F := by
  constructor
  · intro hν
    rw [← toFiniteMeasure_image_probabilityMarginalImage K F]
    exact ⟨ν, hν, rfl⟩
  · intro hν
    rw [← toFiniteMeasure_image_probabilityMarginalImage K F] at hν
    obtain ⟨η, hη, heq⟩ := hν
    have hην : η = ν := by
      apply ProbabilityMeasure.toMeasure_injective
      simpa only [ProbabilityMeasure.toMeasure_comp_toFiniteMeasure_eq_toMeasure] using
        congrArg FiniteMeasure.toMeasure heq
    simpa only [hην] using hη

/-- The weak-Borel selector is also measurable in the actual Giry structure. -/
theorem exists_measurable_coupling_selector [MeasurableSpace X] [OpensMeasurableSpace X]
    (K : ProbabilityMeasure L) {F : Set (L × S)} (hF : IsClosed F)
    (hne : (probabilityCouplings K F).Nonempty)
    {ν : X → ProbabilityMeasure S} (hν : Continuous ν)
    (hνmem : ∀ x, ν x ∈ probabilityMarginalImage K F) :
    ∃ s : X → ProbabilityMeasure (L × S), Measurable s ∧
      ∀ x, (x, s x) ∈ couplingGraph K F ν := by
  obtain ⟨s, hs, hsmem⟩ := exists_borel_coupling_selector K hF hne hν hνmem
  have hmeasure : Measurable (fun x => (s x).toMeasure) :=
    measurable_probability_toMeasure_of_borel.comp hs
  exact ⟨s, hmeasure.subtype_mk, hsmem⟩

end FinitePR.Coupling

namespace FinitePR.Coupling

open MeasureTheory Set

variable {S : Type*} [MetricSpace S] [MeasurableSpace S] [BorelSpace S]
  [CompactSpace S] {N : ℕ}

theorem measurableSet_listHit {B : Set S} (hB : MeasurableSet B) :
    MeasurableSet {z : Fin N → S | ∃ i : Fin N, z i ∈ B} := by
  have heq : {z : Fin N → S | ∃ i : Fin N, z i ∈ B} =
      ⋃ i : Fin N, (fun z : Fin N → S => z i) ⁻¹' B := by
    ext z
    simp
  rw [heq]
  exact MeasurableSet.iUnion (fun i => hB.preimage (measurable_pi_apply i))

/-- Supported coupling marginals satisfy every actual list-hitting inequality. -/
theorem capacity_of_mem_probabilityMarginalImage
    (K : ProbabilityMeasure (Fin N → S)) (ν : ProbabilityMeasure S)
    (hν : ν ∈ probabilityMarginalImage K (listIncidence N))
    {B : Set S} (hB : MeasurableSet B) :
    (ν : Measure S) B ≤ (K : Measure (Fin N → S)) {z | ∃ i : Fin N, z i ∈ B} := by
  obtain ⟨π, hπ, hνmap⟩ := hν
  let H : Set (Fin N → S) := {z | ∃ i : Fin N, z i ∈ B}
  have hH : MeasurableSet H := measurableSet_listHit hB
  have hsub : Prod.snd ⁻¹' B ⊆
      Prod.fst ⁻¹' H ∪ (listIncidence (S := S) N)ᶜ := by
    intro p hp
    by_cases hf : p ∈ listIncidence N
    · rcases hf with ⟨i, hi⟩
      exact Or.inl ⟨i, hi ▸ hp⟩
    · exact Or.inr hf
  have hfst := ((mem_probabilityCouplings_iff K (listIncidence_isClosed N) π).mp hπ).1
  have hzero : (π : Measure ((Fin N → S) × S)) (listIncidence N)ᶜ = 0 :=
    (FiniteMeasure.null_iff_toMeasure_null π.toFiniteMeasure _).mp hπ.2.2
  have hsnd : (π : Measure ((Fin N → S) × S)).map Prod.snd = (ν : Measure S) := by
    simpa only [ProbabilityMeasure.toMeasure_map] using
      congrArg ProbabilityMeasure.toMeasure hνmap
  calc
    (ν : Measure S) B = (π : Measure _) (Prod.snd ⁻¹' B) := by
      rw [← hsnd, Measure.map_apply measurable_snd hB]
    _ ≤ (π : Measure ((Fin N → S) × S))
        (Prod.fst ⁻¹' H ∪ (listIncidence N)ᶜ) := measure_mono hsub
    _ ≤ (π : Measure ((Fin N → S) × S)) (Prod.fst ⁻¹' H) +
        (π : Measure ((Fin N → S) × S)) (listIncidence N)ᶜ :=
      measure_union_le (μ := (π : Measure ((Fin N → S) × S))) _ _
    _ = (K : Measure _) H := by
      rw [hzero, add_zero, ← Measure.map_apply measurable_fst hH, hfst]

end FinitePR.Coupling

namespace FinitePR.Coupling

open MeasureTheory ProbabilityTheory Set

/-- A Giry measurable probability-valued map is an actual Markov kernel. -/
noncomputable def probabilityKernel {X T : Type*}
    [MeasurableSpace X] [MeasurableSpace T]
    (s : X → ProbabilityMeasure T) (hs : Measurable s) : Kernel X T where
  toFun x := (s x : Measure T)
  measurable' := measurable_subtype_coe.comp hs

instance probabilityKernel_isMarkov {X T : Type*}
    [MeasurableSpace X] [MeasurableSpace T]
    (s : X → ProbabilityMeasure T) (hs : Measurable s) :
    IsMarkovKernel (probabilityKernel s hs) := ⟨fun x => by
      change IsProbabilityMeasure (s x : Measure T)
      infer_instance⟩

variable {X L S : Type*} [TopologicalSpace X] [MeasurableSpace X]
  [OpensMeasurableSpace X]
  [MetricSpace L] [MetricSpace S] [CompactSpace L] [CompactSpace S]
  [MeasurableSpace L] [MeasurableSpace S] [BorelSpace L] [BorelSpace S]

/-- The actual chosen probabilities assemble into a Markov coupling kernel. -/
theorem exists_markov_coupling_kernel_of_attainability
    (K : ProbabilityMeasure L) {F : Set (L × S)} (hF : IsClosed F)
    (hne : (probabilityCouplings K F).Nonempty)
    {ν : X → ProbabilityMeasure S} (hν : Continuous ν)
    (hνmem : ∀ x, ν x ∈ probabilityMarginalImage K F) :
    ∃ κ : Kernel X (L × S), IsMarkovKernel κ ∧
      ∀ x, (κ x).map Prod.fst = (K : Measure L) ∧
        (κ x).map Prod.snd = (ν x : Measure S) ∧ κ x F = 1 := by
  obtain ⟨s, hs, hsmem⟩ := exists_measurable_coupling_selector K hF hne hν hνmem
  refine ⟨probabilityKernel s hs, inferInstance, ?_⟩
  intro x
  have hc := (mem_probabilityCouplings_iff K hF (s x)).mp (hsmem x).1
  refine ⟨hc.1, ?_, hc.2⟩
  change (s x : Measure (L × S)).map Prod.snd = (ν x : Measure S)
  simpa only [ProbabilityMeasure.toMeasure_map] using
    congrArg ProbabilityMeasure.toMeasure (hsmem x).2

end FinitePR.Coupling

namespace FinitePR.Coupling

open MeasureTheory ProbabilityTheory Set
open scoped BoundedContinuousFunction

variable {S : Type*} [MetricSpace S] [MeasurableSpace S] [BorelSpace S]
  [CompactSpace S] [Nonempty S] {N : ℕ}

/-- Actual capacity sufficiency, with no prescribed-coupling existence premise. -/
theorem mem_probabilityMarginalImage_of_capacity (hN : 0 < N)
    (K : ProbabilityMeasure (Fin N → S)) (ν : ProbabilityMeasure S)
    (hcap : ∀ B : Set S, MeasurableSet B →
      (ν : Measure S) B ≤ (K : Measure (Fin N → S)) {z | ∃ i : Fin N, z i ∈ B}) :
    ν ∈ probabilityMarginalImage K (listIncidence N) := by
  apply (mem_probabilityMarginalImage_iff K (listIncidence N) ν).mpr
  apply FinitePR.Dual.mem_of_forall_test_exists
    (marginalImage K (listIncidence N))
    (marginalImage_isCompact K (listIncidence_isClosed N))
    (marginalImage_convex K (listIncidence N)) ν.toFiniteMeasure
  intro f
  obtain ⟨η, hη, heq⟩ := exists_maximizing_marginal hN K f
  refine ⟨η, hη, ?_⟩
  rw [heq]
  change (∫ t, f t ∂(ν : Measure S)) ≤ _
  exact integral_le_listMaximum_of_capacity hN K ν hcap f

/-- Exact characterization of attainable finite-list marginals by hitting capacity. -/
theorem mem_probabilityMarginalImage_iff_capacity (hN : 0 < N)
    (K : ProbabilityMeasure (Fin N → S)) (ν : ProbabilityMeasure S) :
    ν ∈ probabilityMarginalImage K (listIncidence N) ↔
      ∀ B : Set S, MeasurableSet B →
        (ν : Measure S) B ≤ (K : Measure (Fin N → S)) {z | ∃ i : Fin N, z i ∈ B} :=
  ⟨fun hν B hB => capacity_of_mem_probabilityMarginalImage K ν hν hB,
    mem_probabilityMarginalImage_of_capacity hN K ν⟩

/-- The capacity inequalities produce an actual probability-one supported coupling. -/
theorem exists_supported_coupling_of_capacity (hN : 0 < N)
    (K : ProbabilityMeasure (Fin N → S)) (ν : ProbabilityMeasure S)
    (hcap : ∀ B : Set S, MeasurableSet B →
      (ν : Measure S) B ≤ (K : Measure (Fin N → S)) {z | ∃ i : Fin N, z i ∈ B}) :
    ∃ π : ProbabilityMeasure ((Fin N → S) × S),
      (π : Measure ((Fin N → S) × S)).map Prod.fst = (K : Measure (Fin N → S)) ∧
      (π : Measure ((Fin N → S) × S)).map Prod.snd = (ν : Measure S) ∧
      (π : Measure ((Fin N → S) × S)) (listIncidence N) = 1 := by
  obtain ⟨π, hπ, hmap⟩ := mem_probabilityMarginalImage_of_capacity hN K ν hcap
  have hc := (mem_probabilityCouplings_iff K (listIncidence_isClosed N) π).mp hπ
  refine ⟨π, hc.1, ?_, hc.2⟩
  simpa only [ProbabilityMeasure.toMeasure_map] using
    congrArg ProbabilityMeasure.toMeasure hmap

theorem exists_list_coupling_kernel_of_capacity
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    (hN : 0 < N) (K : ProbabilityMeasure (Fin N → S))
    {ν : X → ProbabilityMeasure S} (hν : Continuous ν)
    (hcap : ∀ x (B : Set S), MeasurableSet B →
      (ν x : Measure S) B ≤ (K : Measure (Fin N → S)) {z | ∃ i : Fin N, z i ∈ B}) :
    ∃ κ : Kernel X ((Fin N → S) × S), IsMarkovKernel κ ∧
      ∀ x, (κ x).map Prod.fst = (K : Measure _) ∧
        (κ x).map Prod.snd = (ν x : Measure S) ∧ κ x (listIncidence N) = 1 :=
  exists_markov_coupling_kernel_of_attainability K (listIncidence_isClosed N)
    (probabilityCouplings_list_nonempty K hN) hν
    (fun x => mem_probabilityMarginalImage_of_capacity hN K (ν x) (hcap x))

end FinitePR.Coupling

namespace FinitePR.Coupling

open MeasureTheory Set

variable {S : Type*} [MetricSpace S] [MeasurableSpace S] [BorelSpace S] {N : ℕ}

private def matchingPredicate (p : (Fin N → S) × S) (k : ℕ) : Prop :=
  ∃ i : Fin N, i.val = k ∧ p.2 = p.1 i

/-- A total measurable matching-coordinate index, with coordinate zero as fallback. -/
noncomputable def matchingIndex (hN : 0 < N) (p : (Fin N → S) × S) : Fin N := by
  classical
  refine ⟨Nat.findGreatest (matchingPredicate p) (N - 1), ?_⟩
  have hle := Nat.findGreatest_le (P := matchingPredicate p) (N - 1)
  omega

theorem matchingIndex_measurable [SecondCountableTopology S] (hN : 0 < N) :
    Measurable (matchingIndex (S := S) hN) := by
  classical
  have hv : Measurable (fun p : (Fin N → S) × S => (matchingIndex hN p).val) := by
    change Measurable (fun p => Nat.findGreatest (matchingPredicate p) (N - 1))
    apply measurable_findGreatest
    intro k hk
    have hkN : k < N := by omega
    have heq : {p : (Fin N → S) × S | matchingPredicate p k} =
        {p | p.2 = p.1 ⟨k, hkN⟩} := by
      ext p
      constructor
      · rintro ⟨i, hi, hp⟩
        have hieq : i = ⟨k, hkN⟩ := Fin.ext hi
        simpa only [mem_setOf_eq, hieq] using hp
      · intro hp
        exact ⟨⟨k, hkN⟩, rfl, hp⟩
    rw [heq]
    exact (isClosed_eq continuous_snd
      ((continuous_apply (⟨k, hkN⟩ : Fin N)).comp continuous_fst)).measurableSet
  apply measurable_to_countable'
  intro i
  have heq : matchingIndex (S := S) hN ⁻¹' {i} =
      (fun p => (matchingIndex hN p).val) ⁻¹' {i.val} := by
    ext p
    simp only [mem_preimage, mem_singleton_iff, Fin.ext_iff]
  rw [heq]
  exact hv (measurableSet_singleton i.val)

theorem matchingIndex_spec (hN : 0 < N) (p : (Fin N → S) × S)
    (hp : p ∈ listIncidence N) : p.1 (matchingIndex hN p) = p.2 := by
  classical
  obtain ⟨i, hi⟩ := hp
  have hbound : i.val ≤ N - 1 := by omega
  have hpi : matchingPredicate p i.val := ⟨i, rfl, hi⟩
  obtain ⟨j, hj, heq⟩ := Nat.findGreatest_spec hbound hpi
  have hji : j = matchingIndex hN p := Fin.ext hj
  simpa only [hji] using heq.symm

noncomputable def indexEncoding (hN : 0 < N) (p : (Fin N → S) × S) : (Fin N → S) × Fin N :=
  (p.1, matchingIndex hN p)

def indexDecoding (p : (Fin N → S) × Fin N) : (Fin N → S) × S := (p.1, p.1 p.2)

theorem indexEncoding_measurable [SecondCountableTopology S] (hN : 0 < N) :
    Measurable (indexEncoding (S := S) hN) :=
  measurable_fst.prodMk (matchingIndex_measurable hN)

theorem indexDecoding_measurable : Measurable (indexDecoding (S := S) (N := N)) :=
  measurable_fst.prodMk
    (measurable_from_prod_countable_left (fun i : Fin N => measurable_pi_apply i))

theorem indexDecoding_encoding (hN : 0 < N) (p : (Fin N → S) × S)
    (hp : p ∈ listIncidence N) : indexDecoding (indexEncoding hN p) = p :=
  Prod.ext rfl (matchingIndex_spec hN p hp)

end FinitePR.Coupling

namespace FinitePR.Coupling

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval ENNReal ProbabilityTheory

variable {X L T : Type*} [MeasurableSpace X] [MeasurableSpace L] [MeasurableSpace T]
  [MeasurableSpace.CountablyGenerated L] [Nonempty T] [StandardBorelSpace T]

/-- Conditional kernel representation with one fixed independent uniform seed.
The full joint pushforward law, including the unchanged list, is explicit.
-/
theorem exists_seed_pair_representation (K : ProbabilityMeasure L)
    (κ : Kernel X (L × T)) [IsMarkovKernel κ]
    (hfst : ∀ x, (κ x).map Prod.fst = (K : Measure L)) :
    ∃ f : X × (L × I) → T, Measurable f ∧
      ∀ x, Measure.map (fun p : L × I => (p.1, f (x, p)))
        ((K : Measure L).prod (volume : Measure I)) = κ x := by
  obtain ⟨F, hF, hFmap⟩ := Kernel.exists_measurable_map_eq_unitInterval κ.condKernel
  let f : X × (L × I) → T := fun p => F (p.1, p.2.1) p.2.2
  have hf : Measurable f := hF.comp
    ((measurable_fst.prodMk (measurable_fst.comp measurable_snd)).prodMk
      (measurable_snd.comp measurable_snd))
  refine ⟨f, hf, ?_⟩
  intro x
  have hfx : Measurable (fun p : L × I => f (x, p)) :=
    hf.comp (measurable_const.prodMk measurable_id)
  have hg : Measurable (fun p : L × I => (p.1, f (x, p))) :=
    measurable_fst.prodMk hfx
  apply Measure.ext
  intro C hC
  rw [Measure.map_apply hg hC, Measure.prod_apply (hg hC)]
  have hdis := congrArg (fun η : Kernel X (L × T) => η x C)
    (κ.disintegrate κ.condKernel)
  rw [Kernel.compProd_apply hC, Kernel.fst_apply, hfst x] at hdis
  calc
    (∫⁻ l, (volume : Measure I) {u | (l, F (x, l) u) ∈ C} ∂(K : Measure L)) =
        ∫⁻ l, κ.condKernel (x, l) (Prod.mk l ⁻¹' C) ∂(K : Measure L) := by
      apply lintegral_congr
      intro l
      rw [← hFmap (x, l), Measure.map_apply hF.of_uncurry_left
        (hC.preimage measurable_prodMk_left)]
      rfl
    _ = κ x C := hdis

end FinitePR.Coupling

namespace FinitePR.Coupling

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval ProbabilityTheory

variable {X S : Type*} [MeasurableSpace X] [MetricSpace S]
  [MeasurableSpace S] [BorelSpace S] [CompactSpace S] {N : ℕ}

/-- An actual supported coupling kernel yields one jointly measurable finite index sampler. -/
theorem exists_list_index_sampler_from_coupling (hN : 0 < N)
    (K : ProbabilityMeasure (Fin N → S)) (ν : X → ProbabilityMeasure S)
    (κ : Kernel X ((Fin N → S) × S)) [IsMarkovKernel κ]
    (hfst : ∀ x, (κ x).map Prod.fst = (K : Measure (Fin N → S)))
    (hsnd : ∀ x, (κ x).map Prod.snd = (ν x : Measure S))
    (hsupport : ∀ x, κ x (listIncidence N) = 1) :
    ∃ ι : X × ((Fin N → S) × I) → Fin N, Measurable ι ∧
      ∀ x, Measure.map (fun p : (Fin N → S) × I => p.1 (ι (x, p)))
        ((K : Measure (Fin N → S)).prod (volume : Measure I)) = (ν x : Measure S) := by
  letI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  have henc : Measurable (indexEncoding (S := S) hN) := indexEncoding_measurable hN
  have hdec : Measurable (indexDecoding (S := S) (N := N)) := indexDecoding_measurable
  let κi : Kernel X ((Fin N → S) × Fin N) := κ.map (indexEncoding hN)
  letI : IsMarkovKernel κi := Kernel.IsMarkovKernel.map κ henc
  have hifst : ∀ x, (κi x).map Prod.fst = (K : Measure (Fin N → S)) := by
    intro x
    rw [Kernel.map_apply κ henc, Measure.map_map measurable_fst henc]
    change (κ x).map Prod.fst = _
    exact hfst x
  obtain ⟨ι, hι, hpairlaw⟩ := exists_seed_pair_representation K κi hifst
  have hdecodeLaw : ∀ x, (κi x).map indexDecoding = κ x := by
    intro x
    rw [Kernel.map_apply κ henc, Measure.map_map hdec henc]
    have hfull : ∀ᵐ p ∂κ x, p ∈ listIncidence N :=
      (mem_ae_iff_prob_eq_one (listIncidence_isClosed N).measurableSet).mpr (hsupport x)
    have hret : (indexDecoding ∘ indexEncoding hN) =ᵐ[κ x] id := by
      filter_upwards [hfull] with p hp
      exact indexDecoding_encoding hN p hp
    rw [Measure.map_congr hret]
    exact Measure.map_id
  refine ⟨ι, hι, ?_⟩
  intro x
  have heval : Measurable (fun q : (Fin N → S) × Fin N => q.1 q.2) :=
    measurable_from_prod_countable_left (fun i : Fin N => measurable_pi_apply i)
  have hpair : Measurable (fun p : (Fin N → S) × I => (p.1, ι (x, p))) :=
    measurable_fst.prodMk (hι.comp (measurable_const.prodMk measurable_id))
  have hd := congrArg (fun μ : Measure ((Fin N → S) × S) => μ.map Prod.snd)
    (hdecodeLaw x)
  rw [Measure.map_map measurable_snd hdec] at hd
  change (κi x).map (fun q => q.1 q.2) = (κ x).map Prod.snd at hd
  calc
    Measure.map (fun p : (Fin N → S) × I => p.1 (ι (x, p)))
        ((K : Measure (Fin N → S)).prod (volume : Measure I)) =
      Measure.map (fun q : (Fin N → S) × Fin N => q.1 q.2)
        (Measure.map (fun p : (Fin N → S) × I => (p.1, ι (x, p)))
          ((K : Measure (Fin N → S)).prod (volume : Measure I))) := by
      rw [Measure.map_map heval hpair]
      rfl
    _ = (κi x).map (fun q => q.1 q.2) := by rw [hpairlaw x]
    _ = (κ x).map Prod.snd := hd
    _ = (ν x : Measure S) := hsnd x

/-- Exact finite-list sampling from capacity, with a fixed prior and one uniform seed. -/
theorem exists_list_index_sampler_of_capacity [Nonempty S]
    [TopologicalSpace X] [OpensMeasurableSpace X]
    (hN : 0 < N) (K : ProbabilityMeasure (Fin N → S))
    {ν : X → ProbabilityMeasure S} (hν : Continuous ν)
    (hcap : ∀ x (B : Set S), MeasurableSet B →
      (ν x : Measure S) B ≤ (K : Measure (Fin N → S)) {z | ∃ i : Fin N, z i ∈ B}) :
    ∃ ι : X × ((Fin N → S) × I) → Fin N, Measurable ι ∧
      ∀ x, Measure.map (fun p : (Fin N → S) × I => p.1 (ι (x, p)))
        ((K : Measure (Fin N → S)).prod (volume : Measure I)) = (ν x : Measure S) := by
  obtain ⟨κ, hκ, hprops⟩ := exists_list_coupling_kernel_of_capacity hN K hν hcap
  letI : IsMarkovKernel κ := hκ
  exact exists_list_index_sampler_from_coupling hN K ν κ
    (fun x => (hprops x).1) (fun x => (hprops x).2.1) (fun x => (hprops x).2.2)

end FinitePR.Coupling

namespace FinitePR.Sampling

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal unitInterval ProbabilityTheory

variable {S : Type*} [MetricSpace S] [MeasurableSpace S] [BorelSpace S]
  [CompactSpace S] {N : ℕ}

/-- The fixed list really consists of independent draws from the conditioned cells. -/
noncomputable def stratifiedPrior (q : ProbabilityMeasure S) (C : Fin N → Set S)
    (hN : 0 < N) (hmass : ∀ i, (q : Measure S).real (C i) = 1 / (N : ℝ)) :
    ProbabilityMeasure (Fin N → S) := by
  have hne : ∀ i, (q : Measure S) (C i) ≠ 0 := by
    intro i hzero
    have hz : (q : Measure S).real (C i) = 0 := by simp [Measure.real, hzero]
    rw [hmass i] at hz
    have hpos : 0 < 1 / (N : ℝ) := one_div_pos.mpr (Nat.cast_pos.mpr hN)
    linarith
  letI : ∀ i, IsProbabilityMeasure (ProbabilityTheory.cond (q : Measure S) (C i)) :=
    fun i => ProbabilityTheory.cond_isProbabilityMeasure (hne i)
  exact ⟨Measure.pi (fun i => ProbabilityTheory.cond (q : Measure S) (C i)), inferInstance⟩

variable {X : Type*} [MetricSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] [Nonempty S]

/-- An equal-mass stratification and the analytic capacity bounds produce the
actual exact sampler for a normalized jointly continuous density family.
The prior, seed and local index map precede every parameter x.
-/
theorem exists_stratified_index_sampler
    (q : ProbabilityMeasure S) (f : X × S → ℝ) (hf : Continuous f)
    (hnonneg : ∀ x z, 0 ≤ f (x, z))
    (hnormalized : ∀ x, ∫ z, f (x, z) ∂(q : Measure S) = 1)
    (hN : 0 < N) (C : Fin N → Set S) (hC : ∀ i, MeasurableSet (C i))
    (hdisjoint : Pairwise (fun i j => Disjoint (C i) (C j)))
    (hcover : (⋃ i, C i) = univ)
    (hmass : ∀ i, (q : Measure S).real (C i) = 1 / (N : ℝ))
    (M ε δ : ℝ) (hbound : ∀ x z, f (x, z) ≤ M)
    (hpositive : ∀ x, ∃ d, ∀ z ∈ C d, ε ≤ f (x, z))
    (hδ : 0 < δ) (hsmall : M * δ ≤ 1 - Real.exp (-(N : ℝ) * δ))
    (hlarge : Real.exp (1 - (N : ℝ) * δ) ≤ ε / (N : ℝ)) :
    ∃ ι : X × ((Fin N → S) × I) → Fin N, Measurable ι ∧
      ∀ x, Measure.map (fun p : (Fin N → S) × I => p.1 (ι (x, p)))
        ((stratifiedPrior q C hN hmass : Measure (Fin N → S)).prod
          (volume : Measure I)) =
        (q : Measure S).withDensity (fun z => ENNReal.ofReal (f (x, z))) := by
  let K := stratifiedPrior q C hN hmass
  let ν := densityFamily q f hf hnonneg hnormalized
  have hν : Continuous ν := densityFamily_continuous q f hf hnonneg hnormalized
  have hcap : ∀ x (B : Set S), MeasurableSet B →
      (ν x : Measure S) B ≤ (K : Measure (Fin N → S)) {z | ∃ i : Fin N, z i ∈ B} := by
    intro x B hB
    have hfx : Continuous (fun z => f (x, z)) :=
      hf.comp (continuous_const.prodMk continuous_id)
    have hfi : Integrable (fun z => f (x, z)) (q : Measure S) :=
      hfx.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hreal := FinitePR.Capacity.stratified_list_hit_capacity
      (q : Measure S) C hC hdisjoint hcover (N : ℝ) (Nat.cast_pos.mpr hN) hmass
      (fun z => f (x, z)) hfi (hnonneg x) (hnormalized x) M ε δ (hbound x)
      (hpositive x) hδ hsmall hlarge B hB
    change (densityProbability q (fun z => f (x, z)) hfx (hnonneg x)
      (hnormalized x) : Measure S) B ≤ (K : Measure (Fin N → S)) _
    rw [densityProbability_apply q (fun z => f (x, z)) hfx (hnonneg x)
      (hnormalized x) hB,
      ENNReal.ofReal_le_iff_le_toReal (measure_ne_top (K : Measure (Fin N → S)) _)]
    exact hreal
  exact FinitePR.Coupling.exists_list_index_sampler_of_capacity hN K hν hcap

end FinitePR.Sampling

namespace FinitePR.Sphere

open MeasureTheory Set
open scoped unitInterval

noncomputable def localSphereDensity (t : Direction) : ℝ := 4 * max (t.1 2) 0

theorem localSphereDensity_continuous : Continuous localSphereDensity := by
  unfold localSphereDensity
  exact continuous_const.mul
    (((continuous_apply (2 : Fin 3)).comp continuous_subtype_val).max continuous_const)

theorem localSphereDensity_nonneg (t : Direction) : 0 ≤ localSphereDensity t := by
  unfold localSphereDensity
  positivity

/-- The original input-independent local density is normalized under the actual prior. -/
theorem localSphereDensity_normalized :
    (∫ t : Direction, localSphereDensity t ∂(uniformSpherePrior : Measure Direction)) = 1 := by
  change (∫ t : Direction, (4 : ℝ) * max (t.1 2) 0
    ∂(uniformSpherePrior : Measure Direction)) = 1
  rw [integral_const_mul, uniformSpherePrior_positivePart_height]
  norm_num

noncomputable def localSphereProbability : ProbabilityMeasure Direction :=
  FinitePR.Sampling.densityProbability uniformSpherePrior localSphereDensity
    localSphereDensity_continuous localSphereDensity_nonneg localSphereDensity_normalized

end FinitePR.Sphere

namespace FinitePR.Sampling

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal unitInterval ProbabilityTheory

/-- Weighting by a density on the target commutes with its actual pushforward.
Injectivity of the source chart is not needed.
-/
theorem map_density_comp {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure A) (φ : A → B) (hφ : Measurable φ)
    (r : B → ℝ≥0∞) (hr : Measurable r) :
    (μ.withDensity (fun a => r (φ a))).map φ = (μ.map φ).withDensity r := by
  apply Measure.ext
  intro C hC
  rw [Measure.map_apply hφ hC, withDensity_apply _ (hφ hC),
    withDensity_apply _ hC, setLIntegral_map hC hr hφ]

variable {X S T : Type*}
  [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  [MetricSpace S] [CompactSpace S] [MeasurableSpace S] [BorelSpace S]
  [MetricSpace T] [CompactSpace T] [MeasurableSpace T] [BorelSpace T] [Nonempty T]
  {N : ℕ}

/-- Stratifying a compact source and pushing its fixed list through a continuous
chart gives a sampler on the target list alone. It needs no inverse chart or
boundary assignment on the target.
-/
theorem exists_pushed_stratified_index_sampler
    (q : ProbabilityMeasure S) (φ : S → T) (hφ : Continuous φ)
    (f : X × T → ℝ) (hf : Continuous f) (hnonneg : ∀ x t, 0 ≤ f (x, t))
    (hnormalized : ∀ x, ∫ s, f (x, φ s) ∂(q : Measure S) = 1)
    (hN : 0 < N) (C : Fin N → Set S) (hC : ∀ i, MeasurableSet (C i))
    (hdisjoint : Pairwise (fun i j => Disjoint (C i) (C j)))
    (hcover : (⋃ i, C i) = univ)
    (hmass : ∀ i, (q : Measure S).real (C i) = 1 / (N : ℝ))
    (M ε δ : ℝ) (hbound : ∀ x s, f (x, φ s) ≤ M)
    (hpositive : ∀ x, ∃ d, ∀ s ∈ C d, ε ≤ f (x, φ s))
    (hδ : 0 < δ) (hsmall : M * δ ≤ 1 - Real.exp (-(N : ℝ) * δ))
    (hlarge : Real.exp (1 - (N : ℝ) * δ) ≤ ε / (N : ℝ)) :
    ∃ ι : X × ((Fin N → T) × I) → Fin N, Measurable ι ∧
      ∀ x, Measure.map (fun p : (Fin N → T) × I => p.1 (ι (x, p)))
        ((ProbabilityMeasure.map (stratifiedPrior q C hN hmass)
          (fun z i => φ (z i)) : Measure (Fin N → T)).prod (volume : Measure I)) =
        ((q : Measure S).map φ).withDensity (fun t => ENNReal.ofReal (f (x, t))) := by
  let qT : ProbabilityMeasure T := ProbabilityMeasure.map q φ
  have hnormalizedT : ∀ x, ∫ t, f (x, t) ∂(qT : Measure T) = 1 := by
    intro x
    have hrow : Continuous (fun t => f (x, t)) :=
      hf.comp (continuous_const.prodMk continuous_id)
    change (∫ t, f (x, t) ∂(q : Measure S).map φ) = 1
    rw [integral_map hφ.measurable.aemeasurable hrow.aestronglyMeasurable]
    exact hnormalized x
  let ν := densityFamily qT f hf hnonneg hnormalizedT
  let Ksrc := stratifiedPrior q C hN hmass
  let K : ProbabilityMeasure (Fin N → T) :=
    ProbabilityMeasure.map Ksrc (fun z i => φ (z i))
  have hlist : Measurable (fun z : Fin N → S => fun i => φ (z i)) :=
    (continuous_pi (fun i => hφ.comp (continuous_apply i))).measurable
  have hν : Continuous ν := densityFamily_continuous qT f hf hnonneg hnormalizedT
  have hcap : ∀ x (B : Set T), MeasurableSet B →
      (ν x : Measure T) B ≤ (K : Measure (Fin N → T)) {z | ∃ i : Fin N, z i ∈ B} := by
    intro x B hB
    have hrowS : Continuous (fun s => f (x, φ s)) :=
      hf.comp (continuous_const.prodMk hφ)
    have hfi : Integrable (fun s => f (x, φ s)) (q : Measure S) :=
      hrowS.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hreal := FinitePR.Capacity.stratified_list_hit_capacity
      (q : Measure S) C hC hdisjoint hcover (N : ℝ) (Nat.cast_pos.mpr hN) hmass
      (fun s => f (x, φ s)) hfi (fun s => hnonneg x (φ s)) (hnormalized x)
      M ε δ (hbound x) (hpositive x) hδ hsmall hlarge
      (φ ⁻¹' B) (hφ.measurable hB)
    have hνlaw : (ν x : Measure T) =
        ((q : Measure S).withDensity (fun s => ENNReal.ofReal (f (x, φ s)))).map φ := by
      change ((q : Measure S).map φ).withDensity (fun t => ENNReal.ofReal (f (x, t))) = _
      exact (map_density_comp (q : Measure S) φ hφ.measurable
        (fun t => ENNReal.ofReal (f (x, t)))
        (hf.comp (continuous_const.prodMk continuous_id)).measurable.ennreal_ofReal).symm
    rw [hνlaw, Measure.map_apply hφ.measurable hB,
      withDensity_apply _ (hφ.measurable hB),
      ← ofReal_integral_eq_lintegral_ofReal hfi.integrableOn
        (ae_of_all _ (fun s => hnonneg x (φ s)))]
    change ENNReal.ofReal (∫ s in φ ⁻¹' B, f (x, φ s) ∂(q : Measure S)) ≤
      ((Ksrc : Measure (Fin N → S)).map (fun z i => φ (z i)))
        {z | ∃ i : Fin N, z i ∈ B}
    rw [Measure.map_apply hlist (FinitePR.Coupling.measurableSet_listHit hB),
      ENNReal.ofReal_le_iff_le_toReal
        (measure_ne_top (Ksrc : Measure (Fin N → S)) _)]
    exact hreal
  exact FinitePR.Coupling.exists_list_index_sampler_of_capacity hN K hν hcap

end FinitePR.Sampling

namespace FinitePR.Sphere

open MeasureTheory Set
open scoped BigOperators

/-- The actual state-dependent Bloch correlation vector, including the y-sign. -/
noncomputable def stateVector (θ : ℝ) (x : Direction) : Fin 3 → ℝ :=
  ![Real.sin (2 * θ) * x.1 0, -(Real.sin (2 * θ) * x.1 1), x.1 2]

noncomputable def stateDot (θ : ℝ) (x t : Direction) : ℝ :=
  ∑ i, stateVector θ x i * t.1 i

def antipode (t : Direction) : Direction :=
  ⟨fun i => -t.1 i, by simpa only [neg_sq] using t.property⟩

/-- The exact normalized residual-density formula from the construction. -/
noncomputable def residualSphereDensity (θ : ℝ) (p : Direction × Direction) : ℝ :=
  (2 / (1 - Real.cos (2 * θ))) *
    max (|stateDot θ p.1 p.2| - Real.cos (2 * θ) * |p.2.1 2|) 0

theorem stateDot_continuous (θ : ℝ) :
    Continuous (fun p : Direction × Direction => stateDot θ p.1 p.2) := by
  have hx (i : Fin 3) : Continuous (fun p : Direction × Direction => p.1.1 i) :=
    ((continuous_apply i).comp continuous_subtype_val).comp continuous_fst
  have ht (i : Fin 3) : Continuous (fun p : Direction × Direction => p.2.1 i) :=
    ((continuous_apply i).comp continuous_subtype_val).comp continuous_snd
  unfold stateDot
  apply continuous_finsetSum
  intro i _
  fin_cases i
  · exact (continuous_const.mul (hx 0)).mul (ht 0)
  · exact (continuous_const.mul (hx 1)).neg.mul (ht 1)
  · exact (hx 2).mul (ht 2)

theorem residualSphereDensity_continuous (θ : ℝ) :
    Continuous (residualSphereDensity θ) := by
  have ht : Continuous (fun p : Direction × Direction => p.2.1 2) :=
    ((continuous_apply (2 : Fin 3)).comp continuous_subtype_val).comp continuous_snd
  exact continuous_const.mul
    (((stateDot_continuous θ).abs.sub (continuous_const.mul ht.abs)).max continuous_const)

theorem residualSphereDensity_even (θ : ℝ) (x t : Direction) :
    residualSphereDensity θ (x, antipode t) = residualSphereDensity θ (x, t) := by
  have hd : stateDot θ x (antipode t) = -stateDot θ x t := by
    simp only [stateDot, antipode, mul_neg, Finset.sum_neg_distrib]
  unfold residualSphereDensity
  rw [hd]
  simp only [antipode, abs_neg]

theorem stateVector_sq_le_one (θ : ℝ) (x : Direction) :
    (∑ i, stateVector θ x i ^ 2) ≤ 1 := by
  have hx : x.1 0 ^ 2 + x.1 1 ^ 2 + x.1 2 ^ 2 = 1 := by
    simpa only [Fin.sum_univ_three] using x.property
  have hs := Real.sin_sq_add_cos_sq (2 * θ)
  rw [Fin.sum_univ_three]
  change (Real.sin (2 * θ) * x.1 0) ^ 2 +
    (-(Real.sin (2 * θ) * x.1 1)) ^ 2 + x.1 2 ^ 2 ≤ 1
  simp only [neg_sq, mul_pow]
  calc
    _ = (Real.sin (2 * θ) ^ 2 + Real.cos (2 * θ) ^ 2) *
        (x.1 0 ^ 2 + x.1 1 ^ 2) + x.1 2 ^ 2 -
        Real.cos (2 * θ) ^ 2 * (x.1 0 ^ 2 + x.1 1 ^ 2) := by ring
    _ = 1 - Real.cos (2 * θ) ^ 2 * (x.1 0 ^ 2 + x.1 1 ^ 2) := by
      rw [hs]
      nlinarith [hx]
    _ ≤ 1 := sub_le_self _
      (mul_nonneg (sq_nonneg _) (add_nonneg (sq_nonneg _) (sq_nonneg _)))

theorem stateDot_abs_le_one (θ : ℝ) (x t : Direction) : |stateDot θ x t| ≤ 1 := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (stateVector θ x) t.1
  have ht := t.property
  have hstate := stateVector_sq_le_one θ x
  change stateDot θ x t ^ 2 ≤ (∑ i, stateVector θ x i ^ 2) * (∑ i, t.1 i ^ 2) at hcs
  rw [ht, mul_one] at hcs
  have hd : stateDot θ x t ^ 2 ≤ 1 := hcs.trans hstate
  exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩

theorem interior_cos_bounds (θ : ℝ) (hθ : 0 < θ) (hθ' : θ < Real.pi / 4) :
    0 < Real.cos (2 * θ) ∧ Real.cos (2 * θ) < 1 := by
  refine ⟨Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith⟩, ?_⟩
  have hc := Real.cos_lt_cos_of_nonneg_of_le_pi
    (x := (0 : ℝ)) (y := 2 * θ) (by norm_num)
    (by linarith [Real.pi_pos]) (by linarith)
  simpa only [Real.cos_zero] using hc

theorem residualSphereDensity_nonneg (θ : ℝ) (hlt : Real.cos (2 * θ) < 1)
    (p : Direction × Direction) : 0 ≤ residualSphereDensity θ p := by
  unfold residualSphereDensity
  positivity

theorem residualSphereDensity_bound (θ : ℝ) (hc : 0 ≤ Real.cos (2 * θ))
    (hlt : Real.cos (2 * θ) < 1) (p : Direction × Direction) :
    residualSphereDensity θ p ≤ 2 / (1 - Real.cos (2 * θ)) := by
  have hd : |stateDot θ p.1 p.2| - Real.cos (2 * θ) * |p.2.1 2| ≤ 1 := by
    have hn := mul_nonneg hc (abs_nonneg (p.2.1 2))
    linarith [stateDot_abs_le_one θ p.1 p.2]
  have hm : max (|stateDot θ p.1 p.2| - Real.cos (2 * θ) * |p.2.1 2|) 0 ≤ 1 :=
    max_le hd zero_le_one
  unfold residualSphereDensity
  simpa using mul_le_mul_of_nonneg_left hm (by positivity :
    0 ≤ 2 / (1 - Real.cos (2 * θ)))

theorem stateDot_difference_le (θ : ℝ) (x u v : Direction) :
    |stateDot θ x u - stateDot θ x v| ≤ coordinateDistance u v := by
  let w : EuclideanSpace ℝ (Fin 3) := WithLp.toLp 2 (stateVector θ x)
  have hwsq : ‖w‖ ^ 2 ≤ 1 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    exact stateVector_sq_le_one θ x
  have hwnorm : ‖w‖ ≤ 1 := by nlinarith [norm_nonneg w]
  have he : stateDot θ x u - stateDot θ x v =
      inner ℝ w (directionVector u - directionVector v) := by
    simp [stateDot, PiLp.inner_apply, Real.inner_apply, w, directionVector,
      PiLp.sub_apply, Fin.sum_univ_three] <;> ring
  rw [he, coordinateDistance_eq_norm]
  exact (abs_real_inner_le_norm w (directionVector u - directionVector v)).trans
    (by simpa only [one_mul] using
      (mul_le_mul_of_nonneg_right hwnorm
        (norm_nonneg (directionVector u - directionVector v))))

theorem height_difference_le (u v : Direction) :
    |u.1 2 - v.1 2| ≤ coordinateDistance u v := by
  let z : Direction := ⟨![0, 0, 1], by norm_num [Fin.sum_univ_three]⟩
  simpa [blochDot, z, Fin.sum_univ_three] using blochDot_difference_le z u v

/-- Exact uniform Euclidean Lipschitz constant used by the rectangular mesh bound. -/
theorem residualSphereDensity_lipschitz (θ : ℝ) (hc : 0 ≤ Real.cos (2 * θ))
    (hlt : Real.cos (2 * θ) < 1) (x u v : Direction) :
    |residualSphereDensity θ (x, u) - residualSphereDensity θ (x, v)| ≤
      (2 * (1 + Real.cos (2 * θ)) / (1 - Real.cos (2 * θ))) *
        coordinateDistance u v := by
  have hα : 0 ≤ 2 / (1 - Real.cos (2 * θ)) := by positivity
  have hdiff :
      |(|stateDot θ x u| - Real.cos (2 * θ) * |u.1 2|) -
        (|stateDot θ x v| - Real.cos (2 * θ) * |v.1 2|)| ≤
      (1 + Real.cos (2 * θ)) * coordinateDistance u v := by
    calc
      _ = |(|stateDot θ x u| - |stateDot θ x v|) -
          Real.cos (2 * θ) * (|u.1 2| - |v.1 2|)| := by congr 1; ring
      _ ≤ |(|stateDot θ x u| - |stateDot θ x v|)| +
          |Real.cos (2 * θ) * (|u.1 2| - |v.1 2|)| := abs_sub _ _
      _ ≤ |stateDot θ x u - stateDot θ x v| +
          Real.cos (2 * θ) * |u.1 2 - v.1 2| := by
        rw [abs_mul, abs_of_nonneg hc]
        exact add_le_add (abs_abs_sub_abs_le_abs_sub _ _)
          (mul_le_mul_of_nonneg_left (abs_abs_sub_abs_le_abs_sub _ _) hc)
      _ ≤ coordinateDistance u v + Real.cos (2 * θ) * coordinateDistance u v :=
        add_le_add (stateDot_difference_le θ x u v)
          (mul_le_mul_of_nonneg_left (height_difference_le u v) hc)
      _ = (1 + Real.cos (2 * θ)) * coordinateDistance u v := by ring
  unfold residualSphereDensity
  rw [← mul_sub, abs_mul, abs_of_nonneg hα]
  calc
    _ ≤ (2 / (1 - Real.cos (2 * θ))) *
        |(|stateDot θ x u| - Real.cos (2 * θ) * |u.1 2|) -
          (|stateDot θ x v| - Real.cos (2 * θ) * |v.1 2|)| :=
      mul_le_mul_of_nonneg_left (abs_max_sub_max_le_abs _ _ 0) hα
    _ ≤ (2 / (1 - Real.cos (2 * θ))) *
        ((1 + Real.cos (2 * θ)) * coordinateDistance u v) :=
      mul_le_mul_of_nonneg_left hdiff hα
    _ = _ := by ring

end FinitePR.Sphere

namespace FinitePR.Sphere

open MeasureTheory Set
open scoped BigOperators

noncomputable def steeringSphereDensity (θ : ℝ) (p : Direction × Direction) : ℝ :=
  4 * (max ((Real.cos (2 * θ) * p.2.1 2 + stateDot θ p.1 p.2) / 2) 0 +
    max ((Real.cos (2 * θ) * p.2.1 2 - stateDot θ p.1 p.2) / 2) 0)

/-- Actual pointwise local-plus-residual decomposition, including all zero cases. -/
theorem steeringSphereDensity_decomposition (θ : ℝ) (hc : 0 ≤ Real.cos (2 * θ))
    (hlt : Real.cos (2 * θ) < 1) (p : Direction × Direction) :
    steeringSphereDensity θ p = Real.cos (2 * θ) * localSphereDensity p.2 +
      (1 - Real.cos (2 * θ)) * residualSphereDensity θ p := by
  have hne : 1 - Real.cos (2 * θ) ≠ 0 := ne_of_gt (sub_pos.mpr hlt)
  have hcancel : (1 - Real.cos (2 * θ)) * (2 / (1 - Real.cos (2 * θ))) = 2 := by
    field_simp
  have hr : (1 - Real.cos (2 * θ)) * residualSphereDensity θ p =
      2 * max (|stateDot θ p.1 p.2| - Real.cos (2 * θ) * |p.2.1 2|) 0 := by
    unfold residualSphereDensity
    rw [← mul_assoc, hcancel]
  rw [hr]
  unfold steeringSphereDensity localSphereDensity
  linarith [FinitePR.residual_positivePart (Real.cos (2 * θ)) (p.2.1 2)
    (stateDot θ p.1 p.2) hc]

noncomputable def steeringCoordinates (θ : ℝ) (x : Direction) (η : ℝ) : Fin 3 → ℝ :=
  ![η * Real.sin (2 * θ) * x.1 0 / 2,
    -(η * Real.sin (2 * θ) * x.1 1) / 2,
    (Real.cos (2 * θ) + η * x.1 2) / 2]

/-- The actual steering vector has squared norm equal to the squared Born marginal. -/
theorem steeringCoordinates_sq (θ : ℝ) (x : Direction) (η : ℝ) (hη : η ^ 2 = 1) :
    (∑ i, steeringCoordinates θ x η i ^ 2) =
      ((1 + η * Real.cos (2 * θ) * x.1 2) / 2) ^ 2 := by
  have hx : x.1 0 ^ 2 + x.1 1 ^ 2 + x.1 2 ^ 2 = 1 := by
    simpa only [Fin.sum_univ_three] using x.property
  have hxy : x.1 0 ^ 2 + x.1 1 ^ 2 = 1 - x.1 2 ^ 2 := by linarith
  have hs : Real.sin (2 * θ) ^ 2 = 1 - Real.cos (2 * θ) ^ 2 := by
    linarith [Real.sin_sq_add_cos_sq (2 * θ)]
  rw [Fin.sum_univ_three]
  change (η * Real.sin (2 * θ) * x.1 0 / 2) ^ 2 +
    (-(η * Real.sin (2 * θ) * x.1 1) / 2) ^ 2 +
    ((Real.cos (2 * θ) + η * x.1 2) / 2) ^ 2 = _
  calc
    _ = (1 / 4 : ℝ) *
        (η ^ 2 * Real.sin (2 * θ) ^ 2 * (x.1 0 ^ 2 + x.1 1 ^ 2) +
          (Real.cos (2 * θ) + η * x.1 2) ^ 2) := by ring
    _ = _ := by
      rw [hη, one_mul, hs, hxy]
      ring_nf
      rw [hη]
      ring

end FinitePR.Sphere

namespace FinitePR.Sphere

open MeasureTheory Set
open scoped unitInterval

/-- Full finite-list application to the actual residual formula. Normalization of the residual density is an explicit hypothesis of this lemma.
-/
theorem exists_residual_index_sampler_of_normalized
    (θ : ℝ) (hθ : 0 < θ) (hθ' : θ < Real.pi / 4)
    (hnormalized : ∀ x : Direction,
      ∫ t, residualSphereDensity θ (x, t) ∂(uniformSpherePrior : Measure Direction) = 1) :
    ∃ N : ℕ, 0 < N ∧ ∃ K : ProbabilityMeasure (Fin N → Direction),
      ∃ ι : Direction × ((Fin N → Direction) × I) → Fin N, Measurable ι ∧
        ∀ x, Measure.map (fun p : (Fin N → Direction) × I => p.1 (ι (x, p)))
          ((K : Measure (Fin N → Direction)).prod (volume : Measure I)) =
          (uniformSpherePrior : Measure Direction).withDensity
            (fun t => ENNReal.ofReal (residualSphereDensity θ (x, t))) := by
  obtain ⟨hc, hlt⟩ := interior_cos_bounds θ hθ hθ'
  let L : ℝ := 2 * (1 + Real.cos (2 * θ)) / (1 - Real.cos (2 * θ))
  let M : ℝ := 2 / (1 - Real.cos (2 * θ))
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hM : 0 < M := by dsimp [M]; positivity
  obtain ⟨k, hk, δ, hδ, hmesh, hsmall, hlarge⟩ := Square.exists_capacity_size L M hM
  have hN : 0 < k ^ 2 := pow_pos hk _
  have hprior : (Square.referenceProbability : Measure Square.Source).map Square.sphereSample =
      (uniformSpherePrior : Measure Direction) := rfl
  have hsourceNormalized : ∀ x : Direction,
      ∫ p, residualSphereDensity θ (x, Square.sphereSample p)
        ∂Square.referenceMeasure = 1 := by
    intro x
    have hrow : Continuous (fun t : Direction => residualSphereDensity θ (x, t)) :=
      (residualSphereDensity_continuous θ).comp (continuous_const.prodMk continuous_id)
    have hnx := hnormalized x
    rw [← hprior, integral_map Square.continuous_sphereSample.measurable.aemeasurable
      hrow.aestronglyMeasurable] at hnx
    exact hnx
  have hmass : ∀ i : Fin (k ^ 2),
      (Square.referenceProbability : Measure Square.Source).real (Square.finCell k hk i) =
        1 / ((k ^ 2 : ℕ) : ℝ) := by
    intro i
    change Square.referenceMeasure.real (Square.finCell k hk i) = 1 / ((k ^ 2 : ℕ) : ℝ)
    simpa only [Nat.cast_pow] using Square.finCell_real_mass k hk i
  have hpositive : ∀ x : Direction, ∃ d : Fin (k ^ 2),
      ∀ p ∈ Square.finCell k hk d,
        (1 / 2 : ℝ) ≤ residualSphereDensity θ (x, Square.sphereSample p) := by
    intro x
    have hrow : Continuous (fun p : Square.Source =>
        residualSphereDensity θ (x, Square.sphereSample p)) :=
      (residualSphereDensity_continuous θ).comp
        (continuous_const.prodMk Square.continuous_sphereSample)
    have hfi : Integrable (fun p => residualSphereDensity θ (x, Square.sphereSample p))
        Square.referenceMeasure :=
      hrow.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    exact Square.exists_positive_finCell k hk _ hrow hfi (hsourceNormalized x)
      L hL (fun p q => residualSphereDensity_lipschitz θ hc.le hlt x _ _) hmesh
  obtain ⟨ι, hι, hlaw⟩ := FinitePR.Sampling.exists_pushed_stratified_index_sampler
    Square.referenceProbability Square.sphereSample Square.continuous_sphereSample
    (residualSphereDensity θ) (residualSphereDensity_continuous θ)
    (fun x t => residualSphereDensity_nonneg θ hlt (x, t)) hsourceNormalized
    hN (Square.finCell k hk) (Square.measurable_finCell k hk)
    (Square.finCell_disjoint k hk) (Square.finCell_cover k hk) hmass M (1 / 2) δ
    (fun x p => residualSphereDensity_bound θ hc.le hlt (x, Square.sphereSample p))
    hpositive hδ (by simpa only [Nat.cast_pow] using hsmall)
    (by simpa only [Nat.cast_pow] using hlarge)
  refine ⟨k ^ 2, hN,
    ProbabilityMeasure.map
      (FinitePR.Sampling.stratifiedPrior Square.referenceProbability (Square.finCell k hk) hN hmass)
      (fun z i => Square.sphereSample (z i)), ι, hι, ?_⟩
  intro x
  simpa only [hprior] using hlaw x

end FinitePR.Sphere

namespace FinitePR.Sphere

open MeasureTheory Set
open scoped BigOperators

/-- Radial extension of the literal height--longitude chart, in Cartesian coordinates. -/
noncomputable def solidChart (p : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![p 0 * Real.sqrt (1 - (p 1) ^ 2) * Real.cos (p 2),
    p 0 * Real.sqrt (1 - (p 1) ^ 2) * Real.sin (p 2), p 0 * p 1]

def solidDomain : Set (Fin 3 → ℝ) :=
  {p | p 0 ∈ Ioo (0 : ℝ) 1 ∧ p 1 ∈ Ioo (-1 : ℝ) 1 ∧
    p 2 ∈ Ioo (-Real.pi) Real.pi}

theorem measurableSet_solidDomain : MeasurableSet solidDomain := by
  exact ((measurable_pi_apply 0 measurableSet_Ioo).inter
    ((measurable_pi_apply 1 measurableSet_Ioo).inter
      (measurable_pi_apply 2 measurableSet_Ioo)))

noncomputable def solidDerivative (p : Fin 3 → ℝ) :
    (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ) :=
  (Matrix.toLin'
    !![Real.sqrt (1 - (p 1) ^ 2) * Real.cos (p 2),
        -(p 0 * p 1 / Real.sqrt (1 - (p 1) ^ 2)) * Real.cos (p 2),
        -(p 0 * Real.sqrt (1 - (p 1) ^ 2)) * Real.sin (p 2);
      Real.sqrt (1 - (p 1) ^ 2) * Real.sin (p 2),
        -(p 0 * p 1 / Real.sqrt (1 - (p 1) ^ 2)) * Real.sin (p 2),
        p 0 * Real.sqrt (1 - (p 1) ^ 2) * Real.cos (p 2);
      p 1, p 0, 0]).toContinuousLinearMap

theorem solidChart_sq (p : Fin 3 → ℝ) (hh : p 1 ∈ Icc (-1 : ℝ) 1) :
    ∑ i, (solidChart p i) ^ 2 = (p 0) ^ 2 := by
  have hs : 0 ≤ 1 - (p 1) ^ 2 := by nlinarith [hh.1, hh.2]
  simp only [solidChart, Fin.sum_univ_three, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two]
  change (p 0 * Real.sqrt (1 - (p 1) ^ 2) * Real.cos (p 2)) ^ 2 +
    (p 0 * Real.sqrt (1 - (p 1) ^ 2) * Real.sin (p 2)) ^ 2 + (p 0 * p 1) ^ 2 = _
  calc
    _ = (p 0) ^ 2 * (Real.sqrt (1 - (p 1) ^ 2) ^ 2 *
        (Real.cos (p 2) ^ 2 + Real.sin (p 2) ^ 2) + (p 1) ^ 2) := by ring
    _ = (p 0) ^ 2 := by rw [Real.sq_sqrt hs, Real.cos_sq_add_sin_sq]; ring

theorem hasFDerivAt_solidChart (p : Fin 3 → ℝ) (hh : p 1 ∈ Ioo (-1 : ℝ) 1) :
    HasFDerivAt solidChart (solidDerivative p) p := by
  have hs : 0 < 1 - (p 1) ^ 2 := by nlinarith [hh.1, hh.2]
  have hR : Real.sqrt (1 - (p 1) ^ 2) ≠ 0 := (Real.sqrt_pos.2 hs).ne'
  have hdR := ((hasFDerivAt_const (1 : ℝ) p).sub
    ((hasFDerivAt_apply (1 : Fin 3) p).pow 2)).sqrt hs.ne'
  have hdcos := (hasFDerivAt_apply (𝕜 := ℝ) (2 : Fin 3) p).cos
  have hdsin := (hasFDerivAt_apply (𝕜 := ℝ) (2 : Fin 3) p).sin
  apply hasFDerivAt_pi''
  intro i
  fin_cases i
  · convert! ((hasFDerivAt_apply (0 : Fin 3) p).mul hdR).mul hdcos using 1
    ext v
    simp [solidChart, solidDerivative, Matrix.toLin'_apply, Matrix.mulVec,
      dotProduct, Fin.sum_univ_three, ContinuousLinearMap.proj_apply,
      ContinuousLinearMap.comp_apply]
    field_simp
    <;> ring
  · convert! ((hasFDerivAt_apply (0 : Fin 3) p).mul hdR).mul hdsin using 1
    ext v
    simp [solidChart, solidDerivative, Matrix.toLin'_apply, Matrix.mulVec,
      dotProduct, Fin.sum_univ_three, ContinuousLinearMap.proj_apply,
      ContinuousLinearMap.comp_apply]
    field_simp
    <;> ring
  · convert! (hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 3) p).mul
      (hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 3) p) using 1
    ext v
    simp [solidChart, solidDerivative, Matrix.toLin'_apply, Matrix.mulVec,
      dotProduct, Fin.sum_univ_three, ContinuousLinearMap.proj_apply,
      ContinuousLinearMap.comp_apply]
    ring

theorem det_solidDerivative (p : Fin 3 → ℝ) (hh : p 1 ∈ Ioo (-1 : ℝ) 1) :
    (solidDerivative p).det = -(p 0) ^ 2 := by
  have hs : 0 < 1 - (p 1) ^ 2 := by nlinarith [hh.1, hh.2]
  have hR : Real.sqrt (1 - (p 1) ^ 2) ≠ 0 := (Real.sqrt_pos.2 hs).ne'
  have hRsq := Real.sq_sqrt hs.le
  have htrig := Real.cos_sq_add_sin_sq (p 2)
  simp [solidDerivative, LinearMap.det_toContinuousLinearMap,
    LinearMap.det_toLin', Matrix.det_fin_three, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  calc
    _ = -(p 0) ^ 2 * (Real.sqrt (1 - (p 1) ^ 2) ^ 2 + (p 1) ^ 2) *
        (Real.cos (p 2) ^ 2 + Real.sin (p 2) ^ 2) := by
      field_simp
      ring
    _ = -(p 0) ^ 2 := by rw [hRsq, htrig]; ring

theorem solidChart_injOn : InjOn solidChart solidDomain := by
  intro p hp q hq hpq
  have hrSq : (p 0) ^ 2 = (q 0) ^ 2 := by
    rw [← solidChart_sq p ⟨hp.2.1.1.le, hp.2.1.2.le⟩,
      ← solidChart_sq q ⟨hq.2.1.1.le, hq.2.1.2.le⟩, hpq]
  have hr : p 0 = q 0 := by nlinarith [hp.1.1, hq.1.1]
  have hz := congrFun hpq (2 : Fin 3)
  change p 0 * p 1 = q 0 * q 1 at hz
  have hh : p 1 = q 1 := by rw [← hr] at hz; exact (mul_left_cancel₀ hp.1.1.ne') hz
  have hs : 0 < 1 - (p 1) ^ 2 := by nlinarith [hp.2.1.1, hp.2.1.2]
  have hsq : 0 < 1 - (q 1) ^ 2 := by nlinarith [hq.2.1.1, hq.2.1.2]
  have hpolar : polarCoord.symm (p 0 * Real.sqrt (1 - (p 1) ^ 2), p 2) =
      polarCoord.symm (q 0 * Real.sqrt (1 - (q 1) ^ 2), q 2) := by
    apply Prod.ext
    · exact congrFun hpq (0 : Fin 3)
    · exact congrFun hpq (1 : Fin 3)
  have hφ : p 2 = q 2 := congrArg Prod.snd
    (polarCoord.symm.injOn
      (show (p 0 * Real.sqrt (1 - (p 1) ^ 2), p 2) ∈ polarCoord.target from
        ⟨mul_pos hp.1.1 (Real.sqrt_pos.2 hs), hp.2.2⟩)
      (show (q 0 * Real.sqrt (1 - (q 1) ^ 2), q 2) ∈ polarCoord.target from
        ⟨mul_pos hq.1.1 (Real.sqrt_pos.2 hsq), hq.2.2⟩) hpolar)
  ext i
  fin_cases i <;> assumption

/-- The actual radial chart carries density r² to Cartesian volume on its image. -/
theorem solidChart_map_volume :
    Measure.map solidChart
      (((volume : Measure (Fin 3 → ℝ)).restrict solidDomain).withDensity
        (fun p => ENNReal.ofReal ((p 0) ^ 2))) =
      (volume : Measure (Fin 3 → ℝ)).restrict (solidChart '' solidDomain) := by
  have h := map_withDensity_abs_det_fderiv_eq_addHaar
    (volume : Measure (Fin 3 → ℝ)) measurableSet_solidDomain.nullMeasurableSet
    (fun p hp => (hasFDerivAt_solidChart p hp.2.1).hasFDerivWithinAt) solidChart_injOn
  have hden :
      ((volume : Measure (Fin 3 → ℝ)).restrict solidDomain).withDensity
        (fun p => ENNReal.ofReal |(solidDerivative p).det|) =
      ((volume : Measure (Fin 3 → ℝ)).restrict solidDomain).withDensity
        (fun p => ENNReal.ofReal ((p 0) ^ 2)) := by
    apply withDensity_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_solidDomain] with p hp
    rw [det_solidDerivative p hp.2.1, abs_neg, abs_of_nonneg (sq_nonneg _)]
  rw [hden] at h
  exact h

def cartesianBall : Set (Fin 3 → ℝ) := {q | ∑ i, (q i) ^ 2 < 1}

theorem solidChart_mem_ball {p : Fin 3 → ℝ} (hp : p ∈ solidDomain) :
    solidChart p ∈ cartesianBall := by
  change ∑ i, (solidChart p i) ^ 2 < 1
  rw [solidChart_sq p ⟨hp.2.1.1.le, hp.2.1.2.le⟩]
  nlinarith [hp.1.1, hp.1.2]

theorem mem_solidChart_image_of_mem_ball {q : Fin 3 → ℝ}
    (hq : q ∈ cartesianBall) (hy : q 1 ≠ 0) : q ∈ solidChart '' solidDomain := by
  let S : ℝ := ∑ i, (q i) ^ 2
  have hS : 0 < S := by
    dsimp [S]
    rw [Fin.sum_univ_three]
    nlinarith [sq_pos_of_ne_zero hy, sq_nonneg (q 0), sq_nonneg (q 2)]
  let r := Real.sqrt S
  have hr : 0 < r := Real.sqrt_pos.2 hS
  have hrsq : r ^ 2 = S := Real.sq_sqrt hS.le
  have hrlt : r < 1 := by change S < 1 at hq; nlinarith
  let t : Direction := ⟨fun i => q i / r, by
    simp only [div_pow, ← Finset.sum_div]
    change S / r ^ 2 = 1
    rw [hrsq, div_self hS.ne']⟩
  have ht1 : t.1 1 ≠ 0 := div_ne_zero hy hr.ne'
  obtain ⟨p, hφ, hp⟩ := exists_bounded_parameters t
  have hprod : radius p.1 * Real.sin p.2 ≠ 0 := by
    have hcoord := congrFun (congrArg Subtype.val hp) (1 : Fin 3)
    change radius p.1 * Real.sin p.2 = t.1 1 at hcoord
    rwa [hcoord]
  have hR : radius p.1 ≠ 0 := (mul_ne_zero_iff.1 hprod).1
  have hpos : 0 < 1 - (p.1 : ℝ) ^ 2 := by
    have hs := radius_sq p.1
    nlinarith [sq_pos_of_ne_zero hR]
  have hh : (p.1 : ℝ) ∈ Ioo (-1 : ℝ) 1 := by
    constructor <;> nlinarith [p.1.property.1, p.1.property.2]
  have hφ' : p.2 ∈ Ioo (-Real.pi) Real.pi := by
    constructor
    · exact lt_of_le_of_ne hφ.1 (by
        intro heq
        have hzero : Real.sin p.2 = 0 := by rw [← heq]; simp
        exact hprod (by rw [hzero, mul_zero]))
    · exact lt_of_le_of_ne hφ.2 (by
        intro heq
        have hzero : Real.sin p.2 = 0 := by rw [heq]; simp
        exact hprod (by rw [hzero, mul_zero]))
  let a : Fin 3 → ℝ := ![r, (p.1 : ℝ), p.2]
  refine ⟨a, show a ∈ solidDomain from ⟨⟨hr, hrlt⟩, hh, hφ'⟩, ?_⟩
  have hscaled : solidChart a = fun i => r * (parameterDirection p).1 i := by
    ext i
    fin_cases i <;> simp [a, solidChart, parameterDirection, parameterCoordinates, radius]
    <;> ring
  rw [hscaled, hp]
  ext i
  change r * (q i / r) = q i
  field_simp

theorem coordinate_plane_volume_zero :
    (volume : Measure (Fin 3 → ℝ)) {q | q 1 = 0} = 0 := by
  change (Measure.pi (fun _ : Fin 3 => (volume : Measure ℝ))) {q | q 1 = 0} = 0
  exact Measure.pi_hyperplane (fun _ : Fin 3 => (volume : Measure ℝ)) 1 0

theorem solidChart_image_ae_eq_ball :
    solidChart '' solidDomain =ᵐ[(volume : Measure (Fin 3 → ℝ))] cartesianBall := by
  have hne : ∀ᵐ q : Fin 3 → ℝ ∂volume, q 1 ≠ 0 := by
    rw [ae_iff]
    simpa only [not_not] using coordinate_plane_volume_zero
  filter_upwards [hne] with q hq
  apply propext
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact solidChart_mem_ball hp
  · intro hb
    exact mem_solidChart_image_of_mem_ball hb hq

/-- Genuine equality with ordinary volume on the whole Euclidean unit ball. -/
theorem solidChart_map_volume_ball :
    Measure.map solidChart
      (((volume : Measure (Fin 3 → ℝ)).restrict solidDomain).withDensity
        (fun p => ENNReal.ofReal ((p 0) ^ 2))) =
      (volume : Measure (Fin 3 → ℝ)).restrict cartesianBall := by
  rw [solidChart_map_volume, Measure.restrict_congr_set solidChart_image_ae_eq_ball]

open scoped unitInterval

noncomputable def rawAngularChart (p : ℝ × ℝ) : Fin 3 → ℝ :=
  ![Real.sqrt (1 - p.1 ^ 2) * Real.cos p.2,
    Real.sqrt (1 - p.1 ^ 2) * Real.sin p.2, p.1]

theorem continuous_rawAngularChart : Continuous rawAngularChart := by
  apply continuous_pi
  intro i
  fin_cases i <;> simp [rawAngularChart] <;> fun_prop

def angularDomain : Set (ℝ × ℝ) := Ioo (-1 : ℝ) 1 ×ˢ Ioo (-Real.pi) Real.pi

theorem integral_uniformLongitude (g : ℝ → ℝ) :
    (∫ u : I, g (-Real.pi + 2 * Real.pi * (u : ℝ))) =
      (1 / (2 * Real.pi)) * ∫ φ in (-Real.pi)..Real.pi, g φ := by
  rw [unitInterval.volume_def, integral_subtype_comap measurableSet_Icc
    (fun u : ℝ => g (-Real.pi + 2 * Real.pi * u)),
    integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (a := (0 : ℝ)) (b := 1) (by norm_num)]
  have h := intervalIntegral.integral_comp_mul_add (a := (0 : ℝ)) (b := 1)
    (c := (2 * Real.pi)) g (by positivity) (-Real.pi)
  convert h using 1 <;> simp [smul_eq_mul, mul_add, add_comm, add_left_comm, add_assoc]
  congr 1
  ring

/-- The exact angular Jacobian of the original unit-square probability law. -/
theorem uniformSpherePrior_integral_angular (g : (Fin 3 → ℝ) → ℝ) (hg : Continuous g) :
    (∫ t : Direction, g t.1 ∂(uniformSpherePrior : Measure Direction)) =
      (1 / (4 * Real.pi)) * ∫ p in angularDomain, g (rawAngularChart p) := by
  rw [show (uniformSpherePrior : Measure Direction) =
    ((volume : Measure I).prod (volume : Measure I)).map uniformSphereSample from rfl]
  have htest : Continuous (fun t : Direction => g t.1) := hg.comp continuous_subtype_val
  rw [integral_map continuous_uniformSphereSample.measurable.aemeasurable
    htest.aestronglyMeasurable]
  have hsource : Continuous (fun p : I × I => g (uniformSphereSample p).1) :=
    (hg.comp continuous_subtype_val).comp continuous_uniformSphereSample
  rw [integral_prod _
    (hsource.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))]
  change (∫ u : I, ∫ v : I,
    g (rawAngularChart (2 * (u : ℝ) - 1, -Real.pi + 2 * Real.pi * (v : ℝ)))) = _
  have hlon (h : ℝ) :
      (∫ v : I, g (rawAngularChart (h, -Real.pi + 2 * Real.pi * (v : ℝ)))) =
        (1 / (2 * Real.pi)) * ∫ φ in (-Real.pi)..Real.pi,
          g (rawAngularChart (h, φ)) :=
    integral_uniformLongitude (fun φ => g (rawAngularChart (h, φ)))
  simp_rw [hlon]
  rw [integral_const_mul,
    integral_uniformHeight (fun h : ℝ => ∫ φ in (-Real.pi)..Real.pi,
      g (rawAngularChart (h, φ)))]
  have hrow : Continuous (fun p : ℝ × ℝ => g (rawAngularChart p)) :=
    hg.comp continuous_rawAngularChart
  have hi : IntegrableOn (fun p : ℝ × ℝ => g (rawAngularChart p)) angularDomain :=
    (hrow.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
      (Set.prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self)
  rw [show (∫ p in angularDomain, g (rawAngularChart p)) =
      ∫ h in Ioo (-1 : ℝ) 1, ∫ φ in Ioo (-Real.pi) Real.pi,
        g (rawAngularChart (h, φ)) from setIntegral_prod _ hi]
  simp_rw [← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (a := -Real.pi) (b := Real.pi) (by linarith [Real.pi_pos]),
    ← intervalIntegral.integral_of_le (a := (-1 : ℝ)) (b := 1) (by norm_num)]
  ring

noncomputable def tripleEquiv : (Fin 3 → ℝ) ≃ᵐ ℝ × (ℝ × ℝ) :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 0).trans
    (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ) MeasurableEquiv.finTwoArrow)

theorem tripleEquiv_apply (p : Fin 3 → ℝ) : tripleEquiv p = (p 0, (p 1, p 2)) := rfl

theorem tripleEquiv_symm_apply (p : ℝ × (ℝ × ℝ)) :
    tripleEquiv.symm p = ![p.1, p.2.1, p.2.2] := by
  ext i
  fin_cases i <;> rfl

theorem tripleEquiv_measurePreserving : MeasurePreserving tripleEquiv := by
  exact (volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 0).trans
    ((MeasurePreserving.id (volume : Measure ℝ)).prod (volume_preserving_finTwoArrow ℝ))

theorem solidBall_integral_homogeneous (g : (Fin 3 → ℝ) → ℝ) (hg : Continuous g)
    (hhom : ∀ r : ℝ, 0 ≤ r → ∀ v, g (r • v) = r * g v) :
    (∫ q in cartesianBall, g q) =
      Real.pi * ∫ t : Direction, g t.1 ∂(uniformSpherePrior : Measure Direction) := by
  have hdom : tripleEquiv ⁻¹' (Ioo (0 : ℝ) 1 ×ˢ angularDomain) = solidDomain := by
    ext p
    simp [tripleEquiv_apply, solidDomain, angularDomain]
  have hchart (p : Fin 3 → ℝ) : solidChart p = (p 0) • rawAngularChart (p 1, p 2) := by
    ext i
    fin_cases i <;> simp [solidChart, rawAngularChart, Pi.smul_apply] <;> ring
  calc
    _ = ∫ q in solidChart '' solidDomain, g q :=
      setIntegral_congr_set solidChart_image_ae_eq_ball.symm
    _ = ∫ p in solidDomain, |(solidDerivative p).det| • g (solidChart p) :=
      integral_image_eq_integral_abs_det_fderiv_smul volume measurableSet_solidDomain
        (fun p hp => (hasFDerivAt_solidChart p hp.2.1).hasFDerivWithinAt) solidChart_injOn g
    _ = ∫ p in solidDomain, (p 0) ^ 3 * g (rawAngularChart (p 1, p 2)) := by
      apply setIntegral_congr_fun measurableSet_solidDomain
      intro p hp
      dsimp only
      rw [det_solidDerivative p hp.2.1, abs_neg, abs_of_nonneg (sq_nonneg _),
        hchart, hhom (p 0) hp.1.1.le]
      simp only [smul_eq_mul]
      ring
    _ = ∫ p in Ioo (0 : ℝ) 1 ×ˢ angularDomain,
        p.1 ^ 3 * g (rawAngularChart p.2) := by
      have h := tripleEquiv_measurePreserving.setIntegral_preimage_emb
        tripleEquiv.measurableEmbedding
        (fun p : ℝ × (ℝ × ℝ) => p.1 ^ 3 * g (rawAngularChart p.2))
        (Ioo (0 : ℝ) 1 ×ˢ angularDomain)
      simpa only [hdom, tripleEquiv_apply] using h
    _ = (∫ r in Ioo (0 : ℝ) 1, r ^ 3) * ∫ p in angularDomain, g (rawAngularChart p) :=
      setIntegral_prod_mul (μ := (volume : Measure ℝ)) (ν := (volume : Measure (ℝ × ℝ)))
        (fun r : ℝ => r ^ 3) (fun p : ℝ × ℝ => g (rawAngularChart p)) _ _
    _ = Real.pi * ∫ t : Direction, g t.1 ∂(uniformSpherePrior : Measure Direction) := by
      have hr : (∫ r in Ioo (0 : ℝ) 1, r ^ 3) = (1 / 4 : ℝ) := by
        rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by norm_num)]
        norm_num [integral_pow]
      rw [hr, uniformSpherePrior_integral_angular g hg]
      field_simp
      <;> ring

noncomputable def cartesianIsometry
    (A : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3))
    (q : Fin 3 → ℝ) : Fin 3 → ℝ := WithLp.ofLp (A (WithLp.toLp 2 q))

theorem cartesianIsometry_measurePreserving
    (A : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3)) :
    MeasurePreserving (cartesianIsometry A) :=
  (PiLp.volume_preserving_ofLp (Fin 3)).comp
    (A.measurePreserving.comp (PiLp.volume_preserving_toLp (Fin 3)))

theorem cartesianIsometry_ball_preimage
    (A : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3)) :
    cartesianIsometry A ⁻¹' cartesianBall = cartesianBall := by
  ext q
  have hsq : ∑ i, (cartesianIsometry A q i) ^ 2 = ∑ i, (q i) ^ 2 := by
    have h := congrArg (fun r : ℝ => r ^ 2) (A.norm_map (WithLp.toLp 2 q))
    simpa only [EuclideanSpace.real_norm_sq_eq, cartesianIsometry] using h
  simp only [mem_preimage, cartesianBall, mem_setOf_eq, hsq]

noncomputable def cartesianIsometryEquiv
    (A : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3)) :
    (Fin 3 → ℝ) ≃ᵐ (Fin 3 → ℝ) :=
  (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).trans
    (A.toMeasurableEquiv.trans (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).symm)

theorem solidBall_integral_isometry
    (A : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3))
    (g : (Fin 3 → ℝ) → ℝ) :
    (∫ q in cartesianBall, g (cartesianIsometry A q)) = ∫ q in cartesianBall, g q := by
  have he : MeasurableEmbedding (cartesianIsometry A) :=
    (cartesianIsometryEquiv A).measurableEmbedding
  simpa only [cartesianIsometry_ball_preimage A] using
    (cartesianIsometry_measurePreserving A).setIntegral_preimage_emb he g cartesianBall

/-- Homogeneous continuous tests of the actual prior are invariant under every orthogonal map. -/
theorem uniformSpherePrior_integral_isometry_homogeneous
    (A : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3))
    (g : (Fin 3 → ℝ) → ℝ) (hg : Continuous g)
    (hhom : ∀ r : ℝ, 0 ≤ r → ∀ v, g (r • v) = r * g v) :
    (∫ t : Direction, g (cartesianIsometry A t.1) ∂(uniformSpherePrior : Measure Direction)) =
      ∫ t : Direction, g t.1 ∂(uniformSpherePrior : Measure Direction) := by
  have hA : Continuous (cartesianIsometry A) :=
    (PiLp.continuous_ofLp 2 (fun _ : Fin 3 => ℝ)).comp
      (A.continuous.comp (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)))
  have hhA : ∀ r : ℝ, 0 ≤ r → ∀ v,
      (g ∘ cartesianIsometry A) (r • v) = r * (g ∘ cartesianIsometry A) v := by
    intro r hr v
    change g (WithLp.ofLp (A (WithLp.toLp 2 (r • v)))) = _
    rw [WithLp.toLp_smul, A.map_smul, WithLp.ofLp_smul]
    exact hhom r hr _
  have hl := solidBall_integral_homogeneous (g ∘ cartesianIsometry A) (hg.comp hA) hhA
  have hr := solidBall_integral_homogeneous g hg hhom
  have he := solidBall_integral_isometry A g
  change (∫ q in cartesianBall, (g ∘ cartesianIsometry A) q) = _ at he
  rw [hl, hr] at he
  exact mul_left_cancel₀ Real.pi_ne_zero he

noncomputable def cartesianDot (v q : Fin 3 → ℝ) : ℝ := ∑ i, v i * q i

theorem cartesianDot_eq_inner (v q : Fin 3 → ℝ) :
    cartesianDot v q = inner ℝ (WithLp.toLp 2 v) (WithLp.toLp 2 q) := by
  simp [cartesianDot, PiLp.inner_apply, Real.inner_apply, mul_comm]

theorem cartesianDot_isometry
    (A : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3)) (v q : Fin 3 → ℝ) :
    cartesianDot (cartesianIsometry A v) (cartesianIsometry A q) = cartesianDot v q := by
  simpa only [cartesianDot_eq_inner, cartesianIsometry, WithLp.toLp_ofLp] using
    A.inner_map_map (WithLp.toLp 2 v) (WithLp.toLp 2 q)

theorem exists_cartesian_alignment (v : Fin 3 → ℝ) :
    ∃ A : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3),
      ∀ q : Fin 3 → ℝ,
        cartesianDot v q = ‖WithLp.toLp 2 v‖ * cartesianIsometry A q 2 := by
  let e : EuclideanSpace ℝ (Fin 3) := WithLp.toLp 2 ![0, 0, 1]
  have he : ‖e‖ = 1 := by
    have hs : ‖e‖ ^ 2 = 1 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      norm_num [e, Fin.sum_univ_three]
    nlinarith [norm_nonneg e]
  let w : EuclideanSpace ℝ (Fin 3) := ‖WithLp.toLp 2 v‖ • e
  have hw : ‖WithLp.toLp 2 v‖ = ‖w‖ := by
    simp [w, norm_smul, he, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  let A : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3) :=
    Submodule.reflection (ℝ ∙ (WithLp.toLp 2 v - w))ᗮ
  have hAv : A (WithLp.toLp 2 v) = w := Submodule.reflection_sub hw
  have hcoord : cartesianIsometry A v = ![0, 0, ‖WithLp.toLp 2 v‖] := by
    unfold cartesianIsometry
    rw [hAv]
    ext i
    fin_cases i <;> simp [w, e, WithLp.ofLp_smul]
  refine ⟨A, fun q => ?_⟩
  rw [← cartesianDot_isometry A v q, hcoord]
  simp [cartesianDot, Fin.sum_univ_three]

theorem uniformSpherePrior_abs_height :
    (∫ t : Direction, |t.1 2| ∂(uniformSpherePrior : Measure Direction)) = (1 / 2 : ℝ) := by
  rw [uniformSpherePrior_integral_height abs continuous_abs]
  have hc : Continuous (fun h : ℝ => |h|) := continuous_abs
  have hsplit : (∫ h in (-1 : ℝ)..0, |h|) + (∫ h in (0 : ℝ)..1, |h|) =
      ∫ h in (-1 : ℝ)..1, |h| := intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (-1) 0) (hc.intervalIntegrable 0 1)
  have hl : (∫ h in (-1 : ℝ)..0, |h|) = (1 / 2 : ℝ) := by
    calc
      _ = ∫ h in (-1 : ℝ)..0, -h := by
        apply intervalIntegral.integral_congr
        intro h hh
        rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 0)] at hh
        exact abs_of_nonpos hh.2
      _ = 1 / 2 := by rw [intervalIntegral.integral_neg]; norm_num [integral_id]
  have hr : (∫ h in (0 : ℝ)..1, |h|) = (1 / 2 : ℝ) := by
    calc
      _ = ∫ h in (0 : ℝ)..1, h := by
        apply intervalIntegral.integral_congr
        intro h hh
        rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hh
        exact abs_of_nonneg hh.1
      _ = 1 / 2 := by norm_num [integral_id]
  rw [← hsplit, hl, hr]
  norm_num

/-- Arbitrary-vector absolute projection for the concrete height--longitude prior. -/
theorem uniformSpherePrior_abs_projection (v : Fin 3 → ℝ) :
    (∫ t : Direction, |cartesianDot v t.1| ∂(uniformSpherePrior : Measure Direction)) =
      ‖WithLp.toLp 2 v‖ / 2 := by
  obtain ⟨A, hA⟩ := exists_cartesian_alignment v
  have haxis := uniformSpherePrior_integral_isometry_homogeneous A
    (fun q : Fin 3 → ℝ => |q 2|) ((continuous_apply 2).abs)
    (by
      intro r hr q
      simp [Pi.smul_apply, abs_mul, abs_of_nonneg hr])
  calc
    _ = ∫ t : Direction, ‖WithLp.toLp 2 v‖ * |cartesianIsometry A t.1 2|
        ∂(uniformSpherePrior : Measure Direction) := by
      apply integral_congr_ae
      filter_upwards [] with t
      rw [hA, abs_mul, abs_of_nonneg (norm_nonneg _)]
    _ = ‖WithLp.toLp 2 v‖ * (1 / 2) := by
      rw [integral_const_mul, haxis, uniformSpherePrior_abs_height]
    _ = ‖WithLp.toLp 2 v‖ / 2 := by ring

/-- Arbitrary-vector positive projection for exactly the same concrete prior. -/
theorem uniformSpherePrior_positivePart_projection (v : Fin 3 → ℝ) :
    (∫ t : Direction, max (cartesianDot v t.1) 0 ∂(uniformSpherePrior : Measure Direction)) =
      ‖WithLp.toLp 2 v‖ / 4 := by
  obtain ⟨A, hA⟩ := exists_cartesian_alignment v
  have haxis := uniformSpherePrior_integral_isometry_homogeneous A
    (fun q : Fin 3 → ℝ => max (q 2) 0) ((continuous_apply 2).max continuous_const)
    (by
      intro r hr q
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [mul_max_of_nonneg _ _ hr, mul_zero])
  calc
    _ = ∫ t : Direction, ‖WithLp.toLp 2 v‖ * max (cartesianIsometry A t.1 2) 0
        ∂(uniformSpherePrior : Measure Direction) := by
      apply integral_congr_ae
      filter_upwards [] with t
      rw [hA, mul_max_of_nonneg _ _ (norm_nonneg _), mul_zero]
    _ = ‖WithLp.toLp 2 v‖ * (1 / 4) := by
      rw [integral_const_mul, haxis, uniformSpherePrior_positivePart_height]
    _ = ‖WithLp.toLp 2 v‖ / 4 := by ring

theorem continuous_cartesianDot (v : Fin 3 → ℝ) : Continuous (cartesianDot v) := by
  unfold cartesianDot
  fun_prop

theorem steeringCoordinates_dot (θ : ℝ) (x t : Direction) (η : ℝ) :
    cartesianDot (steeringCoordinates θ x η) t.1 =
      (Real.cos (2 * θ) * t.1 2 + η * stateDot θ x t) / 2 := by
  simp [cartesianDot, steeringCoordinates, stateDot, stateVector, Fin.sum_univ_three]
  ring

theorem steeringCoordinates_norm (θ : ℝ) (hc : 0 ≤ Real.cos (2 * θ))
    (hc' : Real.cos (2 * θ) ≤ 1) (x : Direction) (η : ℝ) (hη : η ^ 2 = 1) :
    ‖WithLp.toLp 2 (steeringCoordinates θ x η)‖ =
      (1 + η * Real.cos (2 * θ) * x.1 2) / 2 := by
  have hs : ‖WithLp.toLp 2 (steeringCoordinates θ x η)‖ ^ 2 =
      ((1 + η * Real.cos (2 * θ) * x.1 2) / 2) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    exact steeringCoordinates_sq θ x η hη
  have hx : |x.1 2| ≤ 1 := by
    have hu := x.property
    rw [Fin.sum_univ_three] at hu
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg (x.1 0), sq_nonneg (x.1 1)]
  have hηabs : |η| = 1 := by nlinarith [sq_abs η, abs_nonneg η]
  have hp : |η * Real.cos (2 * θ) * x.1 2| ≤ 1 := by
    calc
      _ = Real.cos (2 * θ) * |x.1 2| := by
        rw [abs_mul, abs_mul, hηabs, abs_of_nonneg hc, one_mul]
      _ ≤ Real.cos (2 * θ) * 1 := mul_le_mul_of_nonneg_left hx hc
      _ ≤ 1 := by simpa using hc'
  have hn : 0 ≤ (1 + η * Real.cos (2 * θ) * x.1 2) / 2 := by
    linarith [(abs_le.mp hp).1]
  nlinarith [norm_nonneg (WithLp.toLp 2 (steeringCoordinates θ x η))]

theorem steeringSphereDensity_normalized (θ : ℝ) (hc : 0 ≤ Real.cos (2 * θ))
    (hc' : Real.cos (2 * θ) ≤ 1) (x : Direction) :
    (∫ t, steeringSphereDensity θ (x, t) ∂(uniformSpherePrior : Measure Direction)) = 1 := by
  let fplus : Direction → ℝ := fun t => max (cartesianDot (steeringCoordinates θ x 1) t.1) 0
  let fminus : Direction → ℝ := fun t => max (cartesianDot (steeringCoordinates θ x (-1)) t.1) 0
  have hfplus : Continuous fplus :=
    ((continuous_cartesianDot _).comp continuous_subtype_val).max continuous_const
  have hfminus : Continuous fminus :=
    ((continuous_cartesianDot _).comp continuous_subtype_val).max continuous_const
  have hiplus : Integrable fplus (uniformSpherePrior : Measure Direction) :=
    hfplus.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have himinus : Integrable fminus (uniformSpherePrior : Measure Direction) :=
    hfminus.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hp : (∫ t, fplus t ∂(uniformSpherePrior : Measure Direction)) =
      (1 + Real.cos (2 * θ) * x.1 2) / 8 := by
    have h := uniformSpherePrior_positivePart_projection (steeringCoordinates θ x 1)
    rw [steeringCoordinates_norm θ hc hc' x 1 (by norm_num)] at h
    norm_num [fplus, div_div] at h ⊢
    exact h
  have hm : (∫ t, fminus t ∂(uniformSpherePrior : Measure Direction)) =
      (1 - Real.cos (2 * θ) * x.1 2) / 8 := by
    have h := uniformSpherePrior_positivePart_projection (steeringCoordinates θ x (-1))
    rw [steeringCoordinates_norm θ hc hc' x (-1) (by norm_num)] at h
    norm_num [fminus, div_div, neg_mul, sub_eq_add_neg] at h ⊢
    exact h
  have hrow : (fun t : Direction => steeringSphereDensity θ (x, t)) =
      fun t => 4 * (fplus t + fminus t) := by
    funext t
    simp [steeringSphereDensity, fplus, fminus, steeringCoordinates_dot, sub_eq_add_neg]
  rw [hrow, integral_const_mul, integral_add hiplus himinus, hp, hm]
  ring

/-- The concrete original residual formula is normalized; no analytic premise remains. -/
theorem residualSphereDensity_normalized (θ : ℝ) (hc : 0 ≤ Real.cos (2 * θ))
    (hlt : Real.cos (2 * θ) < 1) (x : Direction) :
    (∫ t, residualSphereDensity θ (x, t) ∂(uniformSpherePrior : Measure Direction)) = 1 := by
  have hr : Continuous (fun t : Direction => residualSphereDensity θ (x, t)) :=
    (residualSphereDensity_continuous θ).comp (continuous_const.prodMk continuous_id)
  have hil : Integrable (fun t => Real.cos (2 * θ) * localSphereDensity t)
      (uniformSpherePrior : Measure Direction) :=
    (localSphereDensity_continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)).const_mul _
  have hir : Integrable (fun t => (1 - Real.cos (2 * θ)) * residualSphereDensity θ (x, t))
      (uniformSpherePrior : Measure Direction) :=
    (hr.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)).const_mul _
  have hd := steeringSphereDensity_normalized θ hc hlt.le x
  have heq : (fun t : Direction => steeringSphereDensity θ (x, t)) =
      fun t => Real.cos (2 * θ) * localSphereDensity t +
        (1 - Real.cos (2 * θ)) * residualSphereDensity θ (x, t) :=
    funext fun t => steeringSphereDensity_decomposition θ hc hlt (x, t)
  rw [heq, integral_add hil hir, integral_const_mul, integral_const_mul,
    localSphereDensity_normalized] at hd
  nlinarith [sub_pos.mpr hlt]

theorem exists_residual_index_sampler (θ : ℝ) (hθ : 0 < θ) (hθ' : θ < Real.pi / 4) :
    ∃ N : ℕ, 0 < N ∧ ∃ K : ProbabilityMeasure (Fin N → Direction),
      ∃ ι : Direction × ((Fin N → Direction) × I) → Fin N, Measurable ι ∧
        ∀ x, Measure.map (fun p : (Fin N → Direction) × I => p.1 (ι (x, p)))
          ((K : Measure (Fin N → Direction)).prod (volume : Measure I)) =
          (uniformSpherePrior : Measure Direction).withDensity
            (fun t => ENNReal.ofReal (residualSphereDensity θ (x, t))) := by
  obtain ⟨hc, hlt⟩ := interior_cos_bounds θ hθ hθ'
  exact exists_residual_index_sampler_of_normalized θ hθ hθ'
    (residualSphereDensity_normalized θ hc.le hlt)

open Filter
open scoped Topology BoundedContinuousFunction

noncomputable def euclideanNorm (q : Fin 3 → ℝ) : ℝ := ‖WithLp.toLp 2 q‖

theorem continuous_euclideanNorm : Continuous euclideanNorm :=
  (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).norm

theorem euclideanNorm_ne_zero (q : Fin 3 → ℝ) (hq : q ≠ 0) : euclideanNorm q ≠ 0 := by
  rw [euclideanNorm, norm_ne_zero_iff]
  intro h
  exact hq (by simpa using congrArg WithLp.ofLp h)

theorem euclideanNorm_smul (r : ℝ) (q : Fin 3 → ℝ) :
    euclideanNorm (r • q) = |r| * euclideanNorm q := by
  simp [euclideanNorm, WithLp.toLp_smul, norm_smul]

noncomputable def normalizeNonzero (q : {q : Fin 3 → ℝ // q ≠ 0}) : Direction :=
  ⟨fun i => q.1 i / euclideanNorm q.1, by
    simp only [div_pow, ← Finset.sum_div]
    have hs : (∑ i, (q.1 i) ^ 2) = euclideanNorm q.1 ^ 2 := by
      symm
      exact EuclideanSpace.real_norm_sq_eq (WithLp.toLp 2 q.1)
    rw [hs]
    exact div_self (pow_ne_zero 2 (euclideanNorm_ne_zero q.1 q.2))⟩

theorem continuous_normalizeNonzero : Continuous normalizeNonzero := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  exact (((continuous_apply i).comp continuous_subtype_val).div
    (continuous_euclideanNorm.comp continuous_subtype_val)
    (fun q => euclideanNorm_ne_zero q.1 q.2))

/-- Degree-one radial extension of an actual spherical bounded continuous test. -/
noncomputable def radialExtension (f : Direction →ᵇ ℝ) (q : Fin 3 → ℝ) : ℝ := by
  classical
  exact if hq : q = 0 then 0 else euclideanNorm q * f (normalizeNonzero ⟨q, hq⟩)

@[simp] theorem radialExtension_zero (f : Direction →ᵇ ℝ) : radialExtension f 0 = 0 := by
  simp [radialExtension]

theorem radialExtension_bound (f : Direction →ᵇ ℝ) (q : Fin 3 → ℝ) :
    ‖radialExtension f q‖ ≤ euclideanNorm q * ‖f‖ := by
  by_cases hq : q = 0
  · simp [radialExtension, hq, euclideanNorm]
  · have hn : 0 ≤ euclideanNorm q := norm_nonneg (WithLp.toLp 2 q)
    rw [radialExtension, dif_neg hq, norm_mul, Real.norm_of_nonneg hn]
    exact mul_le_mul_of_nonneg_left (f.norm_coe_le_norm _) (norm_nonneg _)

theorem continuous_radialExtension (f : Direction →ᵇ ℝ) : Continuous (radialExtension f) := by
  have hr : Continuous (fun q : {q : Fin 3 → ℝ // q ≠ 0} => radialExtension f q.1) := by
    have heq : (fun q : {q : Fin 3 → ℝ // q ≠ 0} => radialExtension f q.1) =
        fun q => euclideanNorm q.1 * f (normalizeNonzero q) := by
      funext q
      simp [radialExtension, q.2]
    rw [heq]
    exact (continuous_euclideanNorm.comp continuous_subtype_val).mul
      (f.continuous.comp continuous_normalizeNonzero)
  have hon : ContinuousOn (radialExtension f) {q : Fin 3 → ℝ | q ≠ 0} :=
    continuousOn_iff_continuous_restrict.2 hr
  apply continuous_iff_continuousAt.2
  intro q
  by_cases hq : q = 0
  · subst q
    change Tendsto (radialExtension f) (𝓝 (0 : Fin 3 → ℝ)) (𝓝 (radialExtension f 0))
    rw [radialExtension_zero]
    apply squeeze_zero_norm (radialExtension_bound f)
    simpa [euclideanNorm] using
      (continuous_euclideanNorm.continuousAt (x := (0 : Fin 3 → ℝ))).tendsto.mul_const ‖f‖
  · exact hon.continuousAt
      (isOpen_compl_singleton.mem_nhds (show q ∈ ({0}ᶜ : Set (Fin 3 → ℝ)) from hq))

theorem radialExtension_homogeneous (f : Direction →ᵇ ℝ) (r : ℝ) (hr : 0 ≤ r)
    (q : Fin 3 → ℝ) : radialExtension f (r • q) = r * radialExtension f q := by
  by_cases hr0 : r = 0
  · simp [hr0]
  by_cases hq : q = 0
  · simp [hq]
  have hrq : r • q ≠ 0 := smul_ne_zero hr0 hq
  have hn : normalizeNonzero ⟨r • q, hrq⟩ = normalizeNonzero ⟨q, hq⟩ := by
    apply Subtype.ext
    ext i
    change (r * q i) / euclideanNorm (r • q) = q i / euclideanNorm q
    rw [euclideanNorm_smul, abs_of_nonneg hr]
    field_simp
  rw [radialExtension, dif_neg hrq, radialExtension, dif_neg hq,
    euclideanNorm_smul, abs_of_nonneg hr, hn]
  ring

theorem radialExtension_direction (f : Direction →ᵇ ℝ) (t : Direction) :
    radialExtension f t.1 = f t := by
  have hnorm : euclideanNorm t.1 = 1 := norm_directionVector t
  have ht : t.1 ≠ 0 := by
    intro h
    simp [h, euclideanNorm] at hnorm
  have hn : normalizeNonzero ⟨t.1, ht⟩ = t := by
    apply Subtype.ext
    ext i
    change t.1 i / euclideanNorm t.1 = t.1 i
    rw [hnorm, div_one]
  simp [radialExtension, ht, hnorm, hn]

noncomputable def rotateDirection
    (A : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3)) (t : Direction) : Direction :=
  ⟨cartesianIsometry A t.1, by
    have h : ‖A (WithLp.toLp 2 t.1)‖ = 1 :=
      (A.norm_map _).trans (norm_directionVector t)
    have hs := congrArg (fun r : ℝ => r ^ 2) h
    simpa only [EuclideanSpace.real_norm_sq_eq, one_pow, cartesianIsometry] using hs⟩

theorem continuous_rotateDirection
    (A : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3)) :
    Continuous (rotateDirection A) :=
  (((PiLp.continuous_ofLp 2 (fun _ : Fin 3 => ℝ)).comp
    (A.continuous.comp (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)))).comp
      continuous_subtype_val).subtype_mk _

/-- Full orthogonal invariance of the actual height--longitude pushforward probability. -/
theorem uniformSpherePrior_rotateDirection
    (A : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3)) :
    (uniformSpherePrior : Measure Direction).map (rotateDirection A) =
      (uniformSpherePrior : Measure Direction) := by
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  rw [integral_map (continuous_rotateDirection A).measurable.aemeasurable
    f.continuous.aestronglyMeasurable]
  have h := uniformSpherePrior_integral_isometry_homogeneous A (radialExtension f)
    (continuous_radialExtension f) (radialExtension_homogeneous f)
  have hleft : (fun t : Direction => radialExtension f (cartesianIsometry A t.1)) =
      fun t => f (rotateDirection A t) := by
    funext t
    exact radialExtension_direction f (rotateDirection A t)
  simpa only [hleft, radialExtension_direction] using h

end FinitePR.Sphere

namespace FinitePR.Sphere

open MeasureTheory Set
open scoped BigOperators unitInterval

theorem actual_prior_orthogonal_invariant :
    ∀ A : Transport.Orthogonal,
      (uniformSpherePrior : Measure Direction).map (Transport.action A) =
        (uniformSpherePrior : Measure Direction) := by
  intro A
  exact uniformSpherePrior_rotateDirection A

theorem actual_signed_coordinate_moment (b : Direction) (i : Fin 3) :
    (∫ t, t.1 i * Real.sign (blochDot b t) ∂(uniformSpherePrior : Measure Direction)) =
      b.1 i / 2 := Transport.signed_coordinate_moment actual_prior_orthogonal_invariant b i

theorem actual_projection_zero_null (b : Direction) :
    (uniformSpherePrior : Measure Direction) {t | blochDot b t = 0} = 0 :=
  Transport.projection_zero_null actual_prior_orthogonal_invariant b

theorem actual_steering_test_law (v b : Direction) (outcome : ℝ)
    (houtcome : outcome = 1 ∨ outcome = -1) :
    (∫ t, (if positiveTieSign (blochDot b t) = outcome
      then 4 * max (blochDot v t) 0 else 0) ∂(uniformSpherePrior : Measure Direction)) =
      (1 + outcome * blochDot v b) / 2 :=
  Transport.steering_test_law_positive_tie actual_prior_orthogonal_invariant v b outcome houtcome

noncomputable def signBit (r : ℝ) : Bit := if 0 ≤ r then 0 else 1

theorem measurable_signBit : Measurable signBit := by
  exact measurable_const.ite (measurableSet_le measurable_const measurable_id) measurable_const

theorem bitSign_signBit (r : ℝ) : bitSign (signBit r) = positiveTieSign r := by
  by_cases hr : 0 ≤ r <;> simp [signBit, bitSign, positiveTieSign, hr]

theorem bitSign_injective : Function.Injective bitSign := by
  intro a b hab
  by_cases ha : a = 0
  · have hb : b = 0 := by
      by_contra hb
      norm_num [bitSign, ha, hb] at hab
    exact ha.trans hb.symm
  · have hb : b ≠ 0 := by
      intro hb
      norm_num [bitSign, ha, hb] at hab
    exact ((bit_cases a).resolve_left ha).trans ((bit_cases b).resolve_left hb).symm

theorem signBit_eq_iff (r : ℝ) (b : Bit) :
    signBit r = b ↔ positiveTieSign r = bitSign b := by
  rw [← bitSign_signBit]
  exact bitSign_injective.eq_iff.symm

theorem bitSign_cases (a : Bit) : bitSign a = 1 ∨ bitSign a = -1 := by
  by_cases ha : a = 0 <;> simp [bitSign, ha]

theorem bitSign_sq (a : Bit) : (bitSign a) ^ 2 = 1 := by
  by_cases ha : a = 0 <;> simp [bitSign, ha]

theorem steeringCoordinates_ne_zero (θ : ℝ) (hc : 0 ≤ Real.cos (2 * θ))
    (hlt : Real.cos (2 * θ) < 1) (x : Direction) (a : Bit) :
    steeringCoordinates θ x (bitSign a) ≠ 0 := by
  have hn := steeringCoordinates_norm θ hc hlt.le x (bitSign a) (bitSign_sq a)
  have hp : 0 < (1 + bitSign a * Real.cos (2 * θ) * x.1 2) / 2 := by
    have hx := coordinate_abs_le_one x 2
    have habs : |bitSign a * Real.cos (2 * θ) * x.1 2| ≤ Real.cos (2 * θ) := by
      have ha : |bitSign a| = 1 := by rcases bitSign_cases a with h | h <;> rw [h] <;> norm_num
      rw [abs_mul, abs_mul, ha, abs_of_nonneg hc, one_mul]
      exact (mul_le_mul_of_nonneg_left hx hc).trans_eq (mul_one _)
    linarith [(abs_le.mp habs).1]
  intro hz
  simp [hz] at hn
  linarith

/-- Exact joint Born probability as the actual positive steering-vector integral. -/
theorem steering_weight_joint_Born (θ : ℝ) (hc : 0 ≤ Real.cos (2 * θ))
    (hlt : Real.cos (2 * θ) < 1) (x y : Direction) (a b : Bit) :
    (∫ t, (if signBit (blochDot y t) = b
      then 4 * max (cartesianDot (steeringCoordinates θ x (bitSign a)) t.1) 0 else 0)
        ∂(uniformSpherePrior : Measure Direction)) = projectiveProbability θ x y a b := by
  let r := steeringCoordinates θ x (bitSign a)
  have hr : r ≠ 0 := steeringCoordinates_ne_zero θ hc hlt x a
  let v : Direction := normalizeNonzero ⟨r, hr⟩
  let p := euclideanNorm r
  have hp : 0 < p := lt_of_le_of_ne (norm_nonneg _) (euclideanNorm_ne_zero r hr).symm
  have hrp : r = p • v.1 := by
    ext i
    change r i = p * (r i / p)
    field_simp
  have hdot (t : Direction) : cartesianDot r t.1 = p * blochDot v t := by
    rw [hrp]
    simp [cartesianDot, blochDot, Pi.smul_apply, Finset.mul_sum, mul_assoc]
  have hrow : (fun t : Direction => if signBit (blochDot y t) = b
      then 4 * max (cartesianDot r t.1) 0 else 0) =
      fun t => p * (if positiveTieSign (blochDot y t) = bitSign b
        then 4 * max (blochDot v t) 0 else 0) := by
    funext t
    simp only [signBit_eq_iff, hdot]
    have hm := mul_max_of_nonneg (blochDot v t) 0 hp.le
    simp only [mul_zero] at hm
    rw [← hm]
    split_ifs <;> ring
  rw [show steeringCoordinates θ x (bitSign a) = r from rfl, hrow, integral_const_mul,
    actual_steering_test_law v y (bitSign b) (bitSign_cases b)]
  have hnp : p = (1 + bitSign a * Real.cos (2 * θ) * x.1 2) / 2 :=
    steeringCoordinates_norm θ hc hlt.le x (bitSign a) (bitSign_sq a)
  have hprojection := hdot y
  have hsteer := steeringCoordinates_dot θ x y (bitSign a)
  change cartesianDot r y.1 = _ at hsteer
  calc
    p * ((1 + bitSign b * blochDot v y) / 2) =
        (p + bitSign b * cartesianDot r y.1) / 2 := by rw [hprojection]; ring
    _ = projectiveProbability θ x y a b := by
      rw [hnp, hsteer]
      simp [projectiveProbability, stateDot, stateVector, Fin.sum_univ_three]
      ring

noncomputable def steeringWeight (θ : ℝ) (a : Bit) (p : Direction × Direction) : ℝ :=
  4 * max (cartesianDot (steeringCoordinates θ p.1 (bitSign a)) p.2.1) 0

theorem continuous_steeringWeight (θ : ℝ) (a : Bit) : Continuous (steeringWeight θ a) := by
  have heq : steeringWeight θ a = fun p : Direction × Direction =>
      4 * max ((Real.cos (2 * θ) * p.2.1 2 + bitSign a * stateDot θ p.1 p.2) / 2) 0 := by
    funext p
    exact congrArg (fun r : ℝ => 4 * max r 0) (steeringCoordinates_dot θ p.1 p.2 (bitSign a))
  rw [heq]
  have ht : Continuous (fun p : Direction × Direction => p.2.1 2) :=
    ((continuous_apply (2 : Fin 3)).comp continuous_subtype_val).comp continuous_snd
  exact continuous_const.mul
    (((continuous_const.mul ht).add (continuous_const.mul (stateDot_continuous θ))).div_const 2
      |>.max continuous_const)

theorem steeringWeight_nonneg (θ : ℝ) (a : Bit) (p : Direction × Direction) :
    0 ≤ steeringWeight θ a p := by unfold steeringWeight; positivity

theorem steeringWeight_sum (θ : ℝ) (p : Direction × Direction) :
    steeringSphereDensity θ p = steeringWeight θ 0 p + steeringWeight θ 1 p := by
  simp [steeringWeight, steeringCoordinates_dot, steeringSphereDensity, bitSign,
    sub_eq_add_neg]
  ring

theorem steeringSphereDensity_continuous (θ : ℝ) : Continuous (steeringSphereDensity θ) := by
  have heq : steeringSphereDensity θ = fun p => steeringWeight θ 0 p + steeringWeight θ 1 p :=
    funext (steeringWeight_sum θ)
  rw [heq]
  exact (continuous_steeringWeight θ 0).add (continuous_steeringWeight θ 1)

theorem steeringSphereDensity_nonneg (θ : ℝ) (p : Direction × Direction) :
    0 ≤ steeringSphereDensity θ p := by
  rw [steeringWeight_sum]
  exact add_nonneg (steeringWeight_nonneg θ 0 p) (steeringWeight_nonneg θ 1 p)

/-- Actual local conditional response, with a fair response on the zero density. -/
noncomputable def localResponse (θ : ℝ) (p : Direction × Direction) : ℝ :=
  if steeringSphereDensity θ p = 0 then 1 / 2
  else steeringWeight θ 0 p / steeringSphereDensity θ p

theorem measurable_localResponse (θ : ℝ) : Measurable (localResponse θ) := by
  unfold localResponse
  exact measurable_const.ite
    (measurableSet_eq_fun (steeringSphereDensity_continuous θ).measurable measurable_const)
    ((continuous_steeringWeight θ 0).measurable.div
      (steeringSphereDensity_continuous θ).measurable)

theorem localResponse_bounds (θ : ℝ) (p : Direction × Direction) :
    0 ≤ localResponse θ p ∧ localResponse θ p ≤ 1 := by
  have h0 := steeringWeight_nonneg θ 0 p
  have h1 := steeringWeight_nonneg θ 1 p
  have hsum := steeringWeight_sum θ p
  by_cases hz : steeringSphereDensity θ p = 0
  · simp [localResponse, hz]
    norm_num
  · have hpos : 0 < steeringSphereDensity θ p :=
      lt_of_le_of_ne (steeringSphereDensity_nonneg θ p) (Ne.symm hz)
    simp only [localResponse, if_neg hz]
    constructor
    · exact div_nonneg h0 hpos.le
    · exact (div_le_one hpos).2 (by linarith)

theorem localResponse_weighted_zero (θ : ℝ) (p : Direction × Direction) :
    steeringSphereDensity θ p * localResponse θ p = steeringWeight θ 0 p := by
  have h0 := steeringWeight_nonneg θ 0 p
  have h1 := steeringWeight_nonneg θ 1 p
  have hsum := steeringWeight_sum θ p
  by_cases hz : steeringSphereDensity θ p = 0
  · have hw : steeringWeight θ 0 p = 0 := by linarith
    rw [hz, zero_mul, hw]
  · simp only [localResponse, if_neg hz]
    field_simp

noncomputable def responseMass (θ : ℝ) (a : Bit) (p : Direction × Direction) : ℝ :=
  if a = 0 then localResponse θ p else 1 - localResponse θ p

theorem measurable_responseMass (θ : ℝ) (a : Bit) : Measurable (responseMass θ a) := by
  by_cases ha : a = 0
  · have heq : responseMass θ a = localResponse θ := by funext p; simp [responseMass, ha]
    rw [heq]
    exact measurable_localResponse θ
  · have heq : responseMass θ a = fun p => 1 - localResponse θ p := by
      funext p; simp [responseMass, ha]
    rw [heq]
    exact measurable_const.sub (measurable_localResponse θ)

theorem responseMass_bounds (θ : ℝ) (a : Bit) (p : Direction × Direction) :
    0 ≤ responseMass θ a p ∧ responseMass θ a p ≤ 1 := by
  have h := localResponse_bounds θ p
  by_cases ha : a = 0 <;> simp only [responseMass, ha, if_true, if_false] <;>
    constructor <;> linarith

theorem responseMass_weighted (θ : ℝ) (a : Bit) (p : Direction × Direction) :
    steeringSphereDensity θ p * responseMass θ a p = steeringWeight θ a p := by
  rcases bit_cases a with ha | ha
  · rw [ha]
    exact localResponse_weighted_zero θ p
  · rw [ha]
    change steeringSphereDensity θ p * (1 - localResponse θ p) = steeringWeight θ 1 p
    linarith [localResponse_weighted_zero θ p, steeringWeight_sum θ p]

theorem localResponse_residual_support (θ : ℝ) (hc : 0 ≤ Real.cos (2 * θ))
    (hlt : Real.cos (2 * θ) < 1) (x t : Direction)
    (hpos : 0 < residualSphereDensity θ (x, t)) :
    localResponse θ (x, t) = if 0 ≤ stateDot θ x t then 1 else 0 := by
  let u := Real.cos (2 * θ) * t.1 2
  let w := stateDot θ x t
  have hα : 0 < 2 / (1 - Real.cos (2 * θ)) := by positivity
  have hmax : 0 < max (|w| - Real.cos (2 * θ) * |t.1 2|) 0 := by
    change 0 < (2 / (1 - Real.cos (2 * θ))) *
      max (|w| - Real.cos (2 * θ) * |t.1 2|) 0 at hpos
    rcases mul_pos_iff.mp hpos with h | h
    · exact h.2
    · linarith [h.1]
  have hu : |u| = Real.cos (2 * θ) * |t.1 2| := by
    dsimp [u]
    rw [abs_mul, abs_of_nonneg hc]
  have hstrict : |u| < |w| := by
    have h := (lt_max_iff.mp hmax).resolve_right (lt_irrefl (0 : ℝ))
    linarith
  have hD : steeringSphereDensity θ (x, t) =
      4 * (max ((u + w) / 2) 0 + max ((u - w) / 2) 0) := rfl
  have hW : steeringWeight θ 0 (x, t) = 4 * max ((u + w) / 2) 0 := by
    simp [steeringWeight, steeringCoordinates_dot, bitSign, u, w]
  by_cases hw : 0 ≤ w
  · have hplus : 0 < (u + w) / 2 := by
      rw [abs_of_nonneg hw] at hstrict
      linarith [neg_abs_le u]
    have hminus : (u - w) / 2 ≤ 0 := by
      rw [abs_of_nonneg hw] at hstrict
      linarith [le_abs_self u]
    have hDpos : 0 < steeringSphereDensity θ (x, t) := by
      rw [hD, max_eq_left hplus.le, max_eq_right hminus, add_zero]
      positivity
    simp only [localResponse, if_neg hDpos.ne']
    rw [hW, hD, max_eq_left hplus.le, max_eq_right hminus, add_zero]
    rw [div_self (by positivity)]
    simp only [show 0 ≤ stateDot θ x t from hw, if_true]
  · have hw' : w ≤ 0 := (lt_of_not_ge hw).le
    have hplus : (u + w) / 2 ≤ 0 := by
      rw [abs_of_nonpos hw'] at hstrict
      linarith [le_abs_self u]
    have hminus : 0 < (u - w) / 2 := by
      rw [abs_of_nonpos hw'] at hstrict
      linarith [neg_abs_le u]
    have hDpos : 0 < steeringSphereDensity θ (x, t) := by
      rw [hD, max_eq_right hplus, max_eq_left hminus.le, zero_add]
      positivity
    simp only [localResponse, if_neg hDpos.ne']
    rw [hW, max_eq_right hplus, mul_zero, zero_div]
    simp only [show ¬0 ≤ stateDot θ x t from hw, if_false]

/-- The exact local response becomes the deterministic Alice sign on residual support. -/
theorem residual_response_weighted (θ : ℝ) (hc : 0 ≤ Real.cos (2 * θ))
    (hlt : Real.cos (2 * θ) < 1) (x t : Direction) (a : Bit) :
    residualSphereDensity θ (x, t) * responseMass θ a (x, t) =
      if signBit (stateDot θ x t) = a then residualSphereDensity θ (x, t) else 0 := by
  by_cases hz : residualSphereDensity θ (x, t) = 0
  · simp [hz]
  · have hpos : 0 < residualSphereDensity θ (x, t) :=
      lt_of_le_of_ne (residualSphereDensity_nonneg θ hlt (x, t)) (Ne.symm hz)
    have hr := localResponse_residual_support θ hc hlt x t hpos
    rcases bit_cases a with ha | ha
    · rw [ha]
      by_cases hw : 0 ≤ stateDot θ x t <;>
        simp [responseMass, hr, signBit, hw]
    · rw [ha]
      by_cases hw : 0 ≤ stateDot θ x t <;>
        simp [responseMass, hr, signBit, hw]

end FinitePR.Sphere

namespace FinitePR

open MeasureTheory Set
open scoped ENNReal

lemma bounded_measurable_integrable {A : Type*} [MeasurableSpace A] (μ : Measure A)
    [IsFiniteMeasure μ] (f : A → ℝ) (hf : Measurable f) (C : ℝ)
    (hC : ∀ t, |f t| ≤ C) : Integrable f μ := by
  exact ⟨hf.aestronglyMeasurable, HasFiniteIntegral.of_bounded
    (ae_of_all _ fun t => by simpa only [Real.norm_eq_abs] using hC t)⟩

/-- Real-valued conditional PR mass, obtained from the actual finite product law. -/
theorem protocolLaw_real_mass {X Y Ω : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Ω] {N : ℕ}
    (W : ParallelPRWiring X Y Ω N) (μ : Measure Ω) [IsFiniteMeasure μ]
    (x : X) (y : Y) (a b : Bit) :
    (protocolLaw W μ x y {(a, b)}).toReal =
      ∫ ω, ∑ α : Fin N → Bit,
        if protocolOutput W x y (ω, α) = (a, b) then
          1 / (Fintype.card (Fin N → Bit) : ℝ) else 0 ∂μ := by
  classical
  let ν := (PMF.uniformOfFintype (Fin N → Bit)).toMeasure
  let f : Ω × (Fin N → Bit) → ℝ := fun z =>
    if protocolOutput W x y z = (a, b) then 1 else 0
  have hs : MeasurableSet ((protocolOutput W x y) ⁻¹' {(a, b)}) :=
    (measurable_protocolOutput W x y) (measurableSet_singleton _)
  have hf : Measurable f := measurable_const.ite hs measurable_const
  have hfi : Integrable f (μ.prod ν) := bounded_measurable_integrable _ f hf 1
    (fun z => by dsimp [f]; split_ifs <;> norm_num)
  have hrow : ((protocolOutput W x y) ⁻¹' {(a, b)}).indicator
      (fun _ : Ω × (Fin N → Bit) => (1 : ℝ)) = f := by
    funext z
    simp [f, Set.indicator_apply]
  unfold protocolLaw
  rw [Measure.map_apply (measurable_protocolOutput W x y) (measurableSet_singleton _)]
  change (μ.prod ν).real ((protocolOutput W x y) ⁻¹' {(a, b)}) = _
  rw [← integral_indicator_one hs]
  simp only [Set.indicator_apply, Set.mem_preimage, Set.mem_singleton_iff, Pi.one_apply]
  change (∫ z, f z ∂μ.prod ν) = _
  rw [integral_prod f hfi]
  apply integral_congr_ae
  exact ae_of_all _ fun ω => by
    change (∫ α, f (ω, α) ∂(PMF.uniformOfFintype (Fin N → Bit)).toMeasure) = _
    rw [PMF.integral_eq_sum]
    apply Finset.sum_congr rfl
    intro α _
    simp [PMF.uniformOfFintype_apply, f, one_div]

/-- A uniform seed implements the exact local Bernoulli probability. -/
noncomputable def thresholdBit (r u : ℝ) : Bit := if u ≤ r then 0 else 1

theorem measurable_thresholdBit : Measurable (fun p : ℝ × ℝ => thresholdBit p.1 p.2) := by
  unfold thresholdBit
  exact measurable_const.ite (measurableSet_le measurable_snd measurable_fst) measurable_const

theorem integral_thresholdBit (r : ℝ) (hr : 0 ≤ r ∧ r ≤ 1) (a : Bit) :
    (∫ u : unitInterval, (if thresholdBit r (u : ℝ) = a then (1 : ℝ) else 0)
      ∂volume) = if a = 0 then r else 1 - r := by
  let z : unitInterval := ⟨r, hr⟩
  have h0 : (∫ u : unitInterval, (if thresholdBit r (u : ℝ) = 0 then (1 : ℝ) else 0)
      ∂volume) = r := by
    have heq : (fun u : unitInterval => if thresholdBit r (u : ℝ) = 0 then (1 : ℝ) else 0) =
        (Iic z).indicator (1 : unitInterval → ℝ) := by
      funext u
      change (if thresholdBit r (u : ℝ) = 0 then (1 : ℝ) else 0) =
        if (u : ℝ) ≤ r then 1 else 0
      by_cases hu : (u : ℝ) ≤ r <;> simp [thresholdBit, hu]
    rw [heq, integral_indicator_one measurableSet_Iic]
    simp [Measure.real, z, ENNReal.toReal_ofReal hr.1]
  rcases bit_cases a with ha | ha
  · simpa [ha] using h0
  · rw [ha]
    have hm : Measurable (fun u : unitInterval =>
        if thresholdBit r (u : ℝ) = 0 then (1 : ℝ) else 0) :=
      measurable_const.ite
        (measurableSet_eq_fun (measurable_thresholdBit.comp
          (measurable_const.prodMk measurable_subtype_coe)) measurable_const) measurable_const
    have hi := bounded_measurable_integrable volume _ hm 1
      (fun u => by split_ifs <;> norm_num)
    have heq : (fun u : unitInterval => if thresholdBit r (u : ℝ) = 1 then (1 : ℝ) else 0) =
        fun u : unitInterval => 1 - (if thresholdBit r (u : ℝ) = 0 then (1 : ℝ) else 0) := by
      funext u
      by_cases hu : (u : ℝ) ≤ r <;> simp [thresholdBit, hu]
    rw [heq, integral_sub (integrable_const (1 : ℝ)) hi, h0]
    simp

end FinitePR

namespace FinitePR.Sphere

open MeasureTheory Set
open scoped BigOperators ENNReal unitInterval

lemma stateVector_ne_zero (θ : ℝ) (hs : Real.sin (2 * θ) ≠ 0) (x : Direction) :
    stateVector θ x ≠ 0 := by
  intro hz
  have h0 : Real.sin (2 * θ) * x.1 0 = 0 := by
    simpa [stateVector] using congrFun hz (0 : Fin 3)
  have h1 : -(Real.sin (2 * θ) * x.1 1) = 0 := by
    simpa [stateVector] using congrFun hz (1 : Fin 3)
  have h2 : x.1 2 = 0 := by simpa [stateVector] using congrFun hz (2 : Fin 3)
  have hx0 := (mul_eq_zero.mp h0).resolve_left hs
  have hx1 := (mul_eq_zero.mp (neg_eq_zero.mp h1)).resolve_left hs
  have hx := x.property
  simp [Fin.sum_univ_three, hx0, hx1, h2] at hx

lemma cartesianProjection_zero_null (v : Fin 3 → ℝ) (hv : v ≠ 0) :
    (uniformSpherePrior : Measure Direction) {t | cartesianDot v t.1 = 0} = 0 := by
  let n : Direction := normalizeNonzero ⟨v, hv⟩
  let p := euclideanNorm v
  have hp : p ≠ 0 := euclideanNorm_ne_zero v hv
  have hvec : v = p • n.1 := by
    ext i
    change v i = p * (v i / p)
    field_simp
  have hdot (t : Direction) : cartesianDot v t.1 = p * blochDot n t := by
    rw [hvec]
    simp [cartesianDot, blochDot, Pi.smul_apply, Finset.mul_sum, mul_assoc]
  have hset : {t : Direction | cartesianDot v t.1 = 0} = {t | blochDot n t = 0} := by
    ext t
    simp [hdot, hp]
  rw [hset]
  exact actual_projection_zero_null n

lemma signBit_neg (r : ℝ) (hr : r ≠ 0) : signBit (-r) = signBit r + 1 := by
  rcases lt_or_gt_of_ne hr with h | h
  · have hn : ¬0 ≤ r := not_le.mpr h
    simp [signBit, hn, (neg_pos.mpr h).le]
    decide
  · have hn : ¬0 ≤ -r := not_le.mpr (neg_neg_of_pos h)
    simp [signBit, h.le, hn]

lemma signBit_projection_antipodal_ae (v : Fin 3 → ℝ) (hv : v ≠ 0) :
    ∀ᵐ t ∂(uniformSpherePrior : Measure Direction),
      signBit (cartesianDot v (antipodalDirection t).1) =
        signBit (cartesianDot v t.1) + 1 := by
  have hn := measure_eq_zero_iff_ae_notMem.mp (cartesianProjection_zero_null v hv)
  filter_upwards [hn] with t ht
  have hneg : cartesianDot v (antipodalDirection t).1 = -cartesianDot v t.1 := by
    simp [cartesianDot, antipodalDirection, mul_neg, Finset.sum_neg_distrib]
  rw [hneg]
  exact signBit_neg _ ht

noncomputable def localJoint (θ : ℝ) (x y : Direction) (a b : Bit) (t : Direction) : ℝ :=
  if signBit (blochDot y t) = b then localSphereDensity t * responseMass θ a (x, t) else 0

noncomputable def residualJoint (θ : ℝ) (x y : Direction) (a b : Bit) (t : Direction) : ℝ :=
  if signBit (stateDot θ x t) = a ∧ signBit (blochDot y t) = b
    then residualSphereDensity θ (x, t) else 0

lemma measurable_localJoint (θ : ℝ) (x y : Direction) (a b : Bit) :
    Measurable (localJoint θ x y a b) := by
  exact (localSphereDensity_continuous.measurable.mul
    ((measurable_responseMass θ a).comp (measurable_const.prodMk measurable_id))).ite
    (measurableSet_eq_fun (measurable_signBit.comp (measurable_blochDot y)) measurable_const)
    measurable_const

lemma measurable_residualJoint (θ : ℝ) (x y : Direction) (a b : Bit) :
    Measurable (residualJoint θ x y a b) := by
  exact ((residualSphereDensity_continuous θ).measurable.comp
    (measurable_const.prodMk measurable_id)).ite
    ((measurableSet_eq_fun (measurable_signBit.comp
      ((stateDot_continuous θ).measurable.comp (measurable_const.prodMk measurable_id)))
      measurable_const).inter
      (measurableSet_eq_fun (measurable_signBit.comp (measurable_blochDot y)) measurable_const))
    measurable_const

lemma integrable_localJoint (θ : ℝ) (x y : Direction) (a b : Bit) :
    Integrable (localJoint θ x y a b) (uniformSpherePrior : Measure Direction) := by
  apply bounded_measurable_integrable _ _ (measurable_localJoint θ x y a b) 4
  intro t
  have ht := coordinate_abs_le_one t 2
  have hl : 0 ≤ localSphereDensity t := localSphereDensity_nonneg t
  have hL : localSphereDensity t ≤ 4 := by
    unfold localSphereDensity
    have hm : max (t.1 2) 0 ≤ 1 := max_le (le_abs_self _ |>.trans ht) zero_le_one
    linarith
  have hr := responseMass_bounds θ a (x, t)
  unfold localJoint
  split_ifs
  · rw [abs_of_nonneg (mul_nonneg hl hr.1)]
    nlinarith
  · norm_num

lemma integrable_residualJoint (θ : ℝ) (hc : 0 ≤ Real.cos (2 * θ))
    (hlt : Real.cos (2 * θ) < 1) (x y : Direction) (a b : Bit) :
    Integrable (residualJoint θ x y a b) (uniformSpherePrior : Measure Direction) := by
  apply bounded_measurable_integrable _ _ (measurable_residualJoint θ x y a b)
    (2 / (1 - Real.cos (2 * θ)))
  intro t
  unfold residualJoint
  split_ifs
  · rw [abs_of_nonneg (residualSphereDensity_nonneg θ hlt (x, t))]
    exact residualSphereDensity_bound θ hc hlt (x, t)
  · simp only [abs_zero]
    positivity

/-- The actual Born joint law decomposes into the operational local response
and the deterministic residual signs against their concrete densities. -/
theorem jointBorn_mixture (θ : ℝ) (hc : 0 ≤ Real.cos (2 * θ))
    (hlt : Real.cos (2 * θ) < 1) (x y : Direction) (a b : Bit) :
    projectiveProbability θ x y a b =
      Real.cos (2 * θ) * ∫ t, localJoint θ x y a b t ∂(uniformSpherePrior : Measure Direction) +
      (1 - Real.cos (2 * θ)) *
        ∫ t, residualJoint θ x y a b t ∂(uniformSpherePrior : Measure Direction) := by
  rw [← steering_weight_joint_Born θ hc hlt x y a b]
  have heq : (fun t : Direction => if signBit (blochDot y t) = b
      then steeringWeight θ a (x, t) else 0) = fun t =>
        Real.cos (2 * θ) * localJoint θ x y a b t +
        (1 - Real.cos (2 * θ)) * residualJoint θ x y a b t := by
    funext t
    rw [← responseMass_weighted, steeringSphereDensity_decomposition θ hc hlt]
    rw [add_mul, mul_assoc, mul_assoc, residual_response_weighted θ hc hlt]
    unfold localJoint residualJoint
    split_ifs <;> simp_all
  change (∫ t, (if signBit (blochDot y t) = b then steeringWeight θ a (x, t) else 0)
    ∂(uniformSpherePrior : Measure Direction)) = _
  rw [heq, integral_add ((integrable_localJoint θ x y a b).const_mul _)
    ((integrable_residualJoint θ hc hlt x y a b).const_mul _),
    integral_const_mul, integral_const_mul]

/-- Concrete residual joint signs equal the fair XOR kernel of the finite PR wiring. -/
theorem residualJoint_fair_parity (θ : ℝ) (hs : Real.sin (2 * θ) ≠ 0)
    (x y : Direction) (a b : Bit) :
    (∫ t, residualJoint θ x y a b t ∂(uniformSpherePrior : Measure Direction)) =
      ∫ t, (if a + b = signBit (stateDot θ x t) + signBit (blochDot y t)
        then (1 / 2 : ℝ) else 0) * residualSphereDensity θ (x, t)
        ∂(uniformSpherePrior : Measure Direction) := by
  apply Symmetrization.deterministic_pair_eq_fair_parity_integral
    (fun t => residualSphereDensity θ (x, t))
    ((residualSphereDensity_continuous θ).comp (continuous_const.prodMk continuous_id)
      |>.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    (fun t => by
      change residualSphereDensity θ (x, antipode t) = residualSphereDensity θ (x, t)
      exact residualSphereDensity_even θ x t)
    (fun t => signBit (stateDot θ x t)) (fun t => signBit (blochDot y t))
    (measurable_signBit.comp ((stateDot_continuous θ).measurable.comp
      (measurable_const.prodMk measurable_id)))
    (measurable_signBit.comp (measurable_blochDot y))
    (signBit_projection_antipodal_ae (stateVector θ x) (stateVector_ne_zero θ hs x))
    (signBit_projection_antipodal_ae y.1 (by
      intro hy
      have h := y.property
      simp [hy] at h)) a b

end FinitePR.Sphere

namespace FinitePR

open MeasureTheory Set
open scoped ENNReal BigOperators unitInterval

noncomputable def conditionalPRMass {X Y Ω : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Ω] {N : ℕ}
    (W : ParallelPRWiring X Y Ω N) (x : X) (y : Y) (a b : Bit) (ω : Ω) : ℝ :=
  ∑ α : Fin N → Bit, if protocolOutput W x y (ω, α) = (a, b)
    then 1 / (Fintype.card (Fin N → Bit) : ℝ) else 0

lemma measurable_conditionalPRMass {X Y Ω : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Ω] {N : ℕ}
    (W : ParallelPRWiring X Y Ω N) (x : X) (y : Y) (a b : Bit) :
    Measurable (conditionalPRMass W x y a b) := by
  classical
  apply Finset.measurable_sum
  intro α _
  exact measurable_const.ite
    (measurableSet_eq_fun ((measurable_protocolOutput W x y).comp
      (measurable_id.prodMk measurable_const)) measurable_const) measurable_const

/-- A fixed measurable shared branch selects local outputs or the actual PR wiring. -/
noncomputable def branchWiring {X Y Ω : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Ω] {N : ℕ}
    (L : Set Ω) (hL : MeasurableSet L) (A : X × Ω → Bit) (B : Y × Ω → Bit)
    (hA : Measurable A) (hB : Measurable B) (R : ParallelPRWiring X Y Ω N) :
    ParallelPRWiring X Y Ω N := by
  classical
  exact {
    u := fun z => if z.2 ∈ L then 0 else R.u z
    v := fun z => if z.2 ∈ L then 0 else R.v z
    alice := fun z => if z.1.2 ∈ L then A z.1 else R.alice z
    bob := fun z => if z.1.2 ∈ L then B z.1 else R.bob z
    measurable_u := measurable_const.ite (hL.preimage measurable_snd) R.measurable_u
    measurable_v := measurable_const.ite (hL.preimage measurable_snd) R.measurable_v
    measurable_alice := (hA.comp measurable_fst).ite
      (hL.preimage (measurable_snd.comp measurable_fst)) R.measurable_alice
    measurable_bob := (hB.comp measurable_fst).ite
      (hL.preimage (measurable_snd.comp measurable_fst)) R.measurable_bob }

lemma conditionalPRMass_branch_local {X Y Ω : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Ω] {N : ℕ}
    (L : Set Ω) (hL : MeasurableSet L) (A : X × Ω → Bit) (B : Y × Ω → Bit)
    (hA : Measurable A) (hB : Measurable B) (R : ParallelPRWiring X Y Ω N)
    (x : X) (y : Y) (ω : Ω) (hω : ω ∈ L) (a b : Bit) :
    conditionalPRMass (branchWiring L hL A B hA hB R) x y a b ω =
      if (A (x, ω), B (y, ω)) = (a, b) then 1 else 0 := by
  classical
  have hcard : (Fintype.card (Fin N → Bit) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  simp [conditionalPRMass, protocolOutput, branchWiring, hω, hcard]

lemma conditionalPRMass_branch_residual {X Y Ω : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Ω] {N : ℕ}
    (L : Set Ω) (hL : MeasurableSet L) (A : X × Ω → Bit) (B : Y × Ω → Bit)
    (hA : Measurable A) (hB : Measurable B) (R : ParallelPRWiring X Y Ω N)
    (x : X) (y : Y) (ω : Ω) (hω : ω ∉ L) (a b : Bit) :
    conditionalPRMass (branchWiring L hL A B hA hB R) x y a b ω =
      conditionalPRMass R x y a b ω := by
  simp [conditionalPRMass, protocolOutput, branchWiring, hω]

noncomputable def mixtureMeasure {Ω : Type*} [MeasurableSpace Ω]
    (r : ℝ) (μ ν : Measure Ω) : Measure Ω :=
  ENNReal.ofReal r • μ + ENNReal.ofReal (1 - r) • ν

lemma mixtureMeasure_probability {Ω : Type*} [MeasurableSpace Ω]
    (r : ℝ) (hr : 0 ≤ r ∧ r ≤ 1) (μ ν : Measure Ω)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    IsProbabilityMeasure (mixtureMeasure r μ ν) := by
  constructor
  simp only [mixtureMeasure, Measure.add_apply, Measure.smul_apply,
    measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add hr.1 (sub_nonneg.mpr hr.2)]
  norm_num

lemma protocolLaw_mixture {X Y Ω : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Ω] {N : ℕ}
    (W : ParallelPRWiring X Y Ω N) (r : ℝ) (hr : 0 ≤ r ∧ r ≤ 1)
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (x : X) (y : Y) (a b : Bit) :
    (protocolLaw W (mixtureMeasure r μ ν) x y {(a, b)}).toReal =
      r * (protocolLaw W μ x y {(a, b)}).toReal +
        (1 - r) * (protocolLaw W ν x y {(a, b)}).toReal := by
  letI hμ : IsProbabilityMeasure (protocolLaw W μ x y) := protocolLaw_probability W μ x y
  letI hν : IsProbabilityMeasure (protocolLaw W ν x y) := protocolLaw_probability W ν x y
  have hlaw : protocolLaw W (mixtureMeasure r μ ν) x y =
      ENNReal.ofReal r • protocolLaw W μ x y +
      ENNReal.ofReal (1 - r) • protocolLaw W ν x y := by
    unfold protocolLaw mixtureMeasure
    rw [Measure.add_prod, Measure.prod_smul_left, Measure.prod_smul_left,
      Measure.map_add _ _ (measurable_protocolOutput W x y),
      Measure.map_smul _ (measurable_protocolOutput W x y).aemeasurable,
      Measure.map_smul _ (measurable_protocolOutput W x y).aemeasurable]
  rw [hlaw, Measure.add_apply, Measure.smul_apply, Measure.smul_apply]
  simp only [smul_eq_mul]
  rw [ENNReal.toReal_add
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _))
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _))]
  simp [ENNReal.toReal_mul, ENNReal.toReal_ofReal hr.1,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hr.2)]

end FinitePR

namespace FinitePR.Protocol

open MeasureTheory Set Sphere
open scoped ENNReal BigOperators unitInterval

noncomputable def clampSeed (r : ℝ) : I :=
  ⟨max 0 (min 1 r), ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩⟩

lemma continuous_clampSeed : Continuous clampSeed :=
  (continuous_const.max (continuous_const.min continuous_id)).subtype_mk _

lemma clampSeed_coe (u : I) : clampSeed (u : ℝ) = u := by
  apply Subtype.ext
  simp [clampSeed, min_eq_right u.property.2, max_eq_right u.property.1]

variable {N : ℕ}

lemma measurable_joint_blochDot :
    Measurable (fun p : Direction × Direction => blochDot p.1 p.2) := by
  unfold blochDot
  apply Finset.measurable_sum
  intro i _
  exact ((measurable_pi_apply i).comp (measurable_subtype_coe.comp measurable_fst)).mul
    ((measurable_pi_apply i).comp (measurable_subtype_coe.comp measurable_snd))

noncomputable def indexRule
    (ι : Direction × ((Fin N → Direction) × I) → Fin N) :
    Direction × SharedSpace N → Fin N := fun z => ι (z.1, (z.2.1, clampSeed z.2.2.1))

lemma measurable_indexRule
    (ι : Direction × ((Fin N → Direction) × I) → Fin N) (hι : Measurable ι) :
    Measurable (indexRule ι) := by
  exact hι.comp (measurable_fst.prodMk
    ((measurable_fst.comp measurable_snd).prodMk
      (continuous_clampSeed.measurable.comp (measurable_fst.comp
        (measurable_snd.comp measurable_snd)))))

lemma measurable_selectedDirection
    (ι : Direction × ((Fin N → Direction) × I) → Fin N) (hι : Measurable ι) :
    Measurable (fun z : Direction × SharedSpace N => z.2.1 (indexRule ι z)) := by
  have hev : Measurable (fun p : (Fin N → Direction) × Fin N => p.1 p.2) :=
    measurable_from_prod_countable_left fun i => measurable_pi_apply i
  exact hev.comp ((measurable_fst.comp measurable_snd).prodMk (measurable_indexRule ι hι))

noncomputable def residualWiring (θ : ℝ)
    (ι : Direction × ((Fin N → Direction) × I) → Fin N) (hι : Measurable ι) :
    ParallelPRWiring Direction Direction (SharedSpace N) N :=
  oneHotWiring (indexRule ι)
    (fun z => signBit (stateDot θ z.1 (z.2.1 (indexRule ι z))))
    (fun z i => signBit (blochDot z.1 (z.2.1 i)))
    (measurable_indexRule ι hι)
    (measurable_signBit.comp ((stateDot_continuous θ).measurable.comp
      (measurable_fst.prodMk (measurable_selectedDirection ι hι))))
    (measurable_pi_iff.mpr fun i => measurable_signBit.comp
      (measurable_joint_blochDot.comp
        (measurable_fst.prodMk ((measurable_pi_apply i).comp
          (measurable_fst.comp measurable_snd)))))

noncomputable def localAlice (θ : ℝ) (z : Direction × SharedSpace N) : Bit :=
  thresholdBit (localResponse θ (z.1, z.2.2.2.1)) z.2.2.2.2.1

noncomputable def localBob (z : Direction × SharedSpace N) : Bit :=
  signBit (blochDot z.1 z.2.2.2.1)

lemma measurable_localAlice (θ : ℝ) : Measurable (localAlice (N := N) θ) := by
  unfold localAlice
  exact measurable_thresholdBit.comp (((measurable_localResponse θ).comp
    (measurable_fst.prodMk (measurable_fst.comp (measurable_snd.comp
      (measurable_snd.comp measurable_snd))))).prodMk
    (measurable_fst.comp (measurable_snd.comp (measurable_snd.comp
      (measurable_snd.comp measurable_snd)))))

lemma measurable_localBob : Measurable (localBob (N := N)) := by
  unfold localBob
  exact measurable_signBit.comp (measurable_joint_blochDot.comp
    (measurable_fst.prodMk (measurable_fst.comp (measurable_snd.comp
      (measurable_snd.comp measurable_snd)))))

noncomputable def localBranch (N : ℕ) : Set (SharedSpace N) := {ω | ω.2.2.2.2 = 0}

lemma measurableSet_localBranch : MeasurableSet (localBranch N) :=
  measurableSet_eq_fun (by fun_prop) measurable_const

noncomputable def fullWiring (θ : ℝ)
    (ι : Direction × ((Fin N → Direction) × I) → Fin N) (hι : Measurable ι) :
    ParallelPRWiring Direction Direction (SharedSpace N) N :=
  branchWiring (localBranch N) measurableSet_localBranch (localAlice θ) localBob
    (measurable_localAlice θ) measurable_localBob (residualWiring θ ι hι)

/-- Local shared-data embedding: fixed dummy list, actual local sphere law and uniform seed. -/
noncomputable def localEmbed (N : ℕ) (p : Direction × I) : SharedSpace N :=
  ((fun _ => Transport.axis), (0, (p.1, ((p.2 : ℝ), 0))))

/-- Residual shared-data embedding: actual settings-independent list and uniform selector seed. -/
noncomputable def residualEmbed (N : ℕ) (p : (Fin N → Direction) × I) : SharedSpace N :=
  (p.1, ((p.2 : ℝ), (Transport.axis, (0, 1))))

lemma measurable_localEmbed : Measurable (localEmbed N) := by
  unfold localEmbed
  fun_prop

lemma measurable_residualEmbed : Measurable (residualEmbed N) := by
  unfold residualEmbed
  fun_prop

noncomputable def localSharedLaw (N : ℕ) : Measure (SharedSpace N) :=
  Measure.map (localEmbed N) ((localSphereProbability : Measure Direction).prod (volume : Measure I))

noncomputable def residualSharedLaw (K : ProbabilityMeasure (Fin N → Direction)) :
    Measure (SharedSpace N) :=
  Measure.map (residualEmbed N) ((K : Measure (Fin N → Direction)).prod (volume : Measure I))

instance localSharedLaw_probability : IsProbabilityMeasure (localSharedLaw N) := by
  unfold localSharedLaw
  infer_instance

instance residualSharedLaw_probability (K : ProbabilityMeasure (Fin N → Direction)) :
    IsProbabilityMeasure (residualSharedLaw K) := by
  unfold residualSharedLaw
  infer_instance

end FinitePR.Protocol

namespace FinitePR.Protocol

open MeasureTheory Set Sphere
open scoped ENNReal BigOperators unitInterval

variable {N : ℕ}

lemma conditionalPRMass_localEmbed (θ : ℝ)
    (ι : Direction × ((Fin N → Direction) × I) → Fin N) (hι : Measurable ι)
    (x y : Direction) (a b : Bit) (p : Direction × I) :
    conditionalPRMass (fullWiring θ ι hι) x y a b (localEmbed N p) =
      if (thresholdBit (localResponse θ (x, p.1)) (p.2 : ℝ), signBit (blochDot y p.1)) = (a, b)
        then 1 else 0 := by
  have h := conditionalPRMass_branch_local (localBranch N) measurableSet_localBranch
      (localAlice θ) localBob (measurable_localAlice θ) measurable_localBob
      (residualWiring θ ι hι) x y (localEmbed N p)
      (by simp [localEmbed, localBranch]) a b
  change conditionalPRMass (branchWiring (localBranch N) measurableSet_localBranch
    (localAlice θ) localBob (measurable_localAlice θ) measurable_localBob
    (residualWiring θ ι hι)) x y a b (localEmbed N p) = _
  rw [h]
  simp only [localAlice, localBob, localEmbed]
  split_ifs <;> simp_all

lemma conditionalPRMass_residualEmbed (θ : ℝ)
    (ι : Direction × ((Fin N → Direction) × I) → Fin N) (hι : Measurable ι)
    (x y : Direction) (a b : Bit) (p : (Fin N → Direction) × I) :
    conditionalPRMass (fullWiring θ ι hι) x y a b (residualEmbed N p) =
      if a + b = signBit (stateDot θ x (p.1 (ι (x, p)))) +
        signBit (blochDot y (p.1 (ι (x, p)))) then 1 / 2 else 0 := by
  have hr := conditionalPRMass_branch_residual (localBranch N) measurableSet_localBranch
    (localAlice θ) localBob (measurable_localAlice θ) measurable_localBob
    (residualWiring θ ι hι) x y (residualEmbed N p)
    (by simp [residualEmbed, localBranch]) a b
  change conditionalPRMass (branchWiring (localBranch N) measurableSet_localBranch
    (localAlice θ) localBob (measurable_localAlice θ) measurable_localBob
    (residualWiring θ ι hι)) x y a b (residualEmbed N p) = _
  rw [hr]
  unfold conditionalPRMass residualWiring
  rw [oneHotWiring_joint_mass]
  simp only [indexRule, residualEmbed, clampSeed_coe]

/-- Exact joint law of the concrete local branch. The local density and
Alice's conditional threshold are integrated against their actual fixed laws. -/
theorem protocolLaw_local_branch (θ : ℝ)
    (ι : Direction × ((Fin N → Direction) × I) → Fin N) (hι : Measurable ι)
    (x y : Direction) (a b : Bit) :
    (protocolLaw (fullWiring θ ι hι) (localSharedLaw N) x y {(a, b)}).toReal =
      ∫ t, localJoint θ x y a b t ∂(uniformSpherePrior : Measure Direction) := by
  let W := fullWiring θ ι hι
  let f : Direction × I → ℝ := fun p =>
    if (thresholdBit (localResponse θ (x, p.1)) (p.2 : ℝ), signBit (blochDot y p.1)) = (a, b)
      then 1 else 0
  have heq : (fun p : Direction × I => conditionalPRMass W x y a b (localEmbed N p)) = f :=
    funext (conditionalPRMass_localEmbed θ ι hι x y a b)
  have hf : Measurable f := by
    rw [← heq]
    exact (measurable_conditionalPRMass W x y a b).comp measurable_localEmbed
  have hfi : Integrable f ((localSphereProbability : Measure Direction).prod (volume : Measure I)) :=
    bounded_measurable_integrable _ f hf 1 (fun p => by dsimp [f]; split_ifs <;> norm_num)
  calc
    (protocolLaw W (localSharedLaw N) x y {(a, b)}).toReal =
        ∫ p, f p ∂((localSphereProbability : Measure Direction).prod (volume : Measure I)) := by
      rw [protocolLaw_real_mass]
      change (∫ ω, conditionalPRMass W x y a b ω ∂localSharedLaw N) = _
      unfold localSharedLaw
      rw [integral_map_of_stronglyMeasurable measurable_localEmbed
        (measurable_conditionalPRMass W x y a b).stronglyMeasurable]
      apply integral_congr_ae
      exact ae_of_all _ fun p => congrFun heq p
    _ = ∫ t, (if signBit (blochDot y t) = b then responseMass θ a (x, t) else 0)
        ∂(localSphereProbability : Measure Direction) := by
      rw [integral_prod f hfi]
      apply integral_congr_ae
      exact ae_of_all _ fun t => by
        change (∫ u : I, f (t, u) ∂volume) = _
        by_cases hb : signBit (blochDot y t) = b
        · simp only [f, Prod.mk.injEq, hb, and_true, ite_true]
          exact integral_thresholdBit (localResponse θ (x, t)) (localResponse_bounds θ (x, t)) a
        · simp [f, hb]
    _ = ∫ t, localSphereDensity t *
        (if signBit (blochDot y t) = b then responseMass θ a (x, t) else 0)
        ∂(uniformSpherePrior : Measure Direction) :=
      Sampling.densityProbability_integral uniformSpherePrior localSphereDensity
        localSphereDensity_continuous localSphereDensity_nonneg localSphereDensity_normalized _
    _ = ∫ t, localJoint θ x y a b t ∂(uniformSpherePrior : Measure Direction) := by
      apply integral_congr_ae
      exact ae_of_all _ fun t => by unfold localJoint; split_ifs <;> simp_all

/-- Exact joint law of the actual finite-list PR branch. The only law input is
the previously proved concrete selector pushforward, and the primitive is the
checked finite independent product of binary PR boxes. -/
theorem protocolLaw_residual_branch (θ : ℝ) (hc : 0 ≤ Real.cos (2 * θ))
    (hlt : Real.cos (2 * θ) < 1) (hs : Real.sin (2 * θ) ≠ 0)
    (K : ProbabilityMeasure (Fin N → Direction))
    (ι : Direction × ((Fin N → Direction) × I) → Fin N) (hι : Measurable ι)
    (hlaw : ∀ x, Measure.map (fun p : (Fin N → Direction) × I => p.1 (ι (x, p)))
      ((K : Measure (Fin N → Direction)).prod (volume : Measure I)) =
        (uniformSpherePrior : Measure Direction).withDensity
          (fun t => ENNReal.ofReal (residualSphereDensity θ (x, t))))
    (x y : Direction) (a b : Bit) :
    (protocolLaw (fullWiring θ ι hι) (residualSharedLaw K) x y {(a, b)}).toReal =
      ∫ t, residualJoint θ x y a b t ∂(uniformSpherePrior : Measure Direction) := by
  let W := fullWiring θ ι hι
  let P := (K : Measure (Fin N → Direction)).prod (volume : Measure I)
  let g : (Fin N → Direction) × I → Direction := fun p => p.1 (ι (x, p))
  let k : Direction → ℝ := fun t =>
    if a + b = signBit (stateDot θ x t) + signBit (blochDot y t) then 1 / 2 else 0
  have hev : Measurable (fun p : (Fin N → Direction) × Fin N => p.1 p.2) :=
    measurable_from_prod_countable_left fun i => measurable_pi_apply i
  have hg : Measurable g := hev.comp
    (measurable_fst.prodMk (hι.comp (measurable_const.prodMk measurable_id)))
  have hk : Measurable k := measurable_const.ite
    (measurableSet_eq_fun measurable_const
      ((measurable_signBit.comp ((stateDot_continuous θ).measurable.comp
        (measurable_const.prodMk measurable_id))).add
        (measurable_signBit.comp (measurable_blochDot y)))) measurable_const
  calc
    (protocolLaw W (residualSharedLaw K) x y {(a, b)}).toReal = ∫ p, k (g p) ∂P := by
      rw [protocolLaw_real_mass]
      change (∫ ω, conditionalPRMass W x y a b ω ∂residualSharedLaw K) = _
      unfold residualSharedLaw
      rw [integral_map_of_stronglyMeasurable measurable_residualEmbed
        (measurable_conditionalPRMass W x y a b).stronglyMeasurable]
      apply integral_congr_ae
      exact ae_of_all _ fun p => conditionalPRMass_residualEmbed θ ι hι x y a b p
    _ = ∫ t, residualSphereDensity θ (x, t) * k t
        ∂(uniformSpherePrior : Measure Direction) :=
      SamplerIntegral.integral_comp_eq_density_mul P (uniformSpherePrior : Measure Direction)
        g hg (fun t => residualSphereDensity θ (x, t))
        ((residualSphereDensity_continuous θ).measurable.comp
          (measurable_const.prodMk measurable_id))
        (fun t => residualSphereDensity_nonneg θ hlt (x, t)) (hlaw x) k hk
    _ = ∫ t, residualJoint θ x y a b t ∂(uniformSpherePrior : Measure Direction) := by
      rw [residualJoint_fair_parity θ hs x y a b]
      apply integral_congr_ae
      exact ae_of_all _ fun t => by change _ * k t = k t * _; ring

end FinitePR.Protocol

namespace FinitePR

open MeasureTheory Sphere Protocol
open scoped ENNReal unitInterval

/-- The original interior-angle, all-projective-direction finite PR simulation.
The shared measure and finite number of boxes are chosen before both settings;
all local response maps are jointly measurable, and every joint Born outcome
is reproduced by the actual independent binary PR product law. -/
theorem partially_entangled_pr_simulability : PartiallyEntangledPRSimulability := by
  intro θ hθ hθ'
  obtain ⟨hc, hlt⟩ := interior_cos_bounds θ hθ hθ'
  have hs : Real.sin (2 * θ) ≠ 0 :=
    (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])).ne'
  obtain ⟨N, hN, K, ι, hι, hlaw⟩ := exists_residual_index_sampler θ hθ hθ'
  let μ : Measure (SharedSpace N) :=
    mixtureMeasure (Real.cos (2 * θ)) (localSharedLaw N) (residualSharedLaw K)
  have hμ : IsProbabilityMeasure μ :=
    mixtureMeasure_probability _ ⟨hc.le, hlt.le⟩ _ _
  refine ⟨N, μ, hμ, fullWiring θ ι hι, ?_⟩
  intro x y a b
  change (protocolLaw (fullWiring θ ι hι)
    (mixtureMeasure (Real.cos (2 * θ)) (localSharedLaw N) (residualSharedLaw K))
      x y {(a, b)}).toReal = _
  rw [protocolLaw_mixture _ _ ⟨hc.le, hlt.le⟩,
    protocolLaw_local_branch, protocolLaw_residual_branch θ hc.le hlt hs K ι hι hlaw]
  exact (jointBorn_mixture θ hc.le hlt x y a b).symm

/-- Literal complex matrix Born rule for the original state and projectors. -/
theorem exact_born_simulation (θ : ℝ) (hθ : 0 < θ) (hθ' : θ < Real.pi / 4) :
    ∃ (N : ℕ) (μ : Measure (SharedSpace N)), IsProbabilityMeasure μ ∧
      ∃ W : ParallelPRWiring Direction Direction (SharedSpace N) N,
        ∀ (x y : Direction) (a b : Bit),
          ((protocolLaw W μ x y {(a, b)}).toReal : ℂ) =
            Matrix.trace (qubitDensity θ *
              Matrix.kronecker (projectiveMatrix a x) (projectiveMatrix b y)) := by
  obtain ⟨N, μ, hμ, W, hW⟩ := partially_entangled_pr_simulability θ hθ hθ'
  refine ⟨N, μ, hμ, W, ?_⟩
  intro x y a b
  rw [born_trace_eq_projectiveProbability, hW]

end FinitePR
