import Mathlib
import QuantumProver.InformationTheory.WernerEndpoint.AntisymmetricStates

set_option autoImplicit false

noncomputable section

namespace QuantumProver.DepolarizingSquashedEntanglement

open Matrix
open scoped BigOperators ComplexOrder Kronecker Matrix.Norms.L2Operator
  ContinuousFunctionalCalculus

abbrev QMatrix (I : Type*) := Matrix I I ℂ
abbrev Qubit := Fin 2
abbrev CanonicalEnvironment := Fin 4

structure Density (I : Type*) [Fintype I] [DecidableEq I] where
  matrix : QMatrix I
  positive : matrix.PosSemidef
  trace_one : Matrix.trace matrix = 1

def pureDensity {I : Type*} (v : I → ℂ) : QMatrix I :=
  QuantumProver.WernerEndpoint.pureDensity v

def vectorNormSq {I : Type*} [Fintype I] (v : I → ℂ) : ℝ :=
  QuantumProver.WernerEndpoint.vectorNormSq v

def IsNormalized {I : Type*} [Fintype I] (v : I → ℂ) : Prop :=
  vectorNormSq v = 1

def partialTraceRight {I J : Type*} [Fintype J]
    (ρ : QMatrix (I × J)) : QMatrix I :=
  QuantumProver.WernerEndpoint.partialTraceLeft ρ

def partialTraceLeft {I J : Type*} [Fintype I]
    (ρ : QMatrix (I × J)) : QMatrix J :=
  QuantumProver.WernerEndpoint.partialTraceRight ρ

theorem partialTraceRight_trace {I J : Type*} [Fintype I] [Fintype J]
    (ρ : QMatrix (I × J)) : Matrix.trace (partialTraceRight ρ) = Matrix.trace ρ :=
  QuantumProver.WernerEndpoint.partialTraceLeft_trace ρ

theorem partialTraceLeft_trace {I J : Type*} [Fintype I] [Fintype J]
    (ρ : QMatrix (I × J)) : Matrix.trace (partialTraceLeft ρ) = Matrix.trace ρ :=
  QuantumProver.WernerEndpoint.partialTraceRight_trace ρ

theorem partialTraceRight_positive {I J : Type*} [Fintype I] [Fintype J]
    {ρ : QMatrix (I × J)} (hρ : ρ.PosSemidef) :
    (partialTraceRight ρ).PosSemidef :=
  QuantumProver.WernerEndpoint.partialTraceLeft_posSemidef ρ hρ

theorem partialTraceLeft_positive {I J : Type*} [Fintype I] [Fintype J]
    {ρ : QMatrix (I × J)} (hρ : ρ.PosSemidef) :
    (partialTraceLeft ρ).PosSemidef :=
  QuantumProver.WernerEndpoint.partialTraceRight_posSemidef ρ hρ

def entropyNat {I : Type*} [Fintype I] [DecidableEq I] (ρ : QMatrix I) : ℝ :=
  (Matrix.trace (cfc Real.negMulLog ρ)).re

def entropyBits {I : Type*} [Fintype I] [DecidableEq I] (ρ : QMatrix I) : ℝ :=
  entropyNat ρ / Real.log 2

def traceMiddle {A B E : Type*} [Fintype B]
    (ρ : QMatrix ((A × B) × E)) : QMatrix (A × E) :=
  fun x y => ∑ b, ρ ((x.1, b), x.2) ((y.1, b), y.2)

def traceFirst {A B E : Type*} [Fintype A]
    (ρ : QMatrix ((A × B) × E)) : QMatrix (B × E) :=
  fun x y => ∑ a, ρ ((a, x.1), x.2) ((a, y.1), y.2)

def cmiNat {A B E : Type*} [Fintype A] [Fintype B] [Fintype E]
    [DecidableEq A] [DecidableEq B] [DecidableEq E]
    (ρ : QMatrix ((A × B) × E)) : ℝ :=
  entropyNat (traceMiddle ρ) + entropyNat (traceFirst ρ) -
    entropyNat (partialTraceLeft ρ) - entropyNat ρ

def cmiBits {A B E : Type*} [Fintype A] [Fintype B] [Fintype E]
    [DecidableEq A] [DecidableEq B] [DecidableEq E]
    (ρ : QMatrix ((A × B) × E)) : ℝ := cmiNat ρ / Real.log 2

def hsSq {I J : Type*} [Fintype I] [Fintype J]
    (M : Matrix I J ℂ) : ℝ := (Matrix.trace (M.conjTranspose * M)).re

def IsIsometry {I O : Type*} [Fintype O] [DecidableEq I]
    (V : Matrix O I ℂ) : Prop := V.conjTranspose * V = 1

def binaryPinch {I J : Type*} (ρ : QMatrix (Sum I J)) : QMatrix (Sum I J) :=
  fun x y => match x, y with
  | Sum.inl _, Sum.inl _ => ρ x y
  | Sum.inr _, Sum.inr _ => ρ x y
  | _, _ => 0

def binaryCoherenceNat {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (ρ : QMatrix (Sum I J)) : ℝ :=
  entropyNat (binaryPinch ρ) - entropyNat ρ

def Fcal (m : ℝ) : ℝ :=
  if m = 2 then 2 else Real.arcosh (m / 2) * Real.sqrt ((m + 2) / (m - 2))

def amplify {I O R : Type*}
    (Φ : QMatrix I →ₗ[ℂ] QMatrix O) (ρ : QMatrix (R × I)) : QMatrix (R × O) :=
  fun x y => Φ (fun i j => ρ (x.1, i) (y.1, j)) x.2 y.2

def IsCompletelyPositive {I O : Type*} [Fintype I] [Fintype O]
    (Φ : QMatrix I →ₗ[ℂ] QMatrix O) : Prop :=
  ∀ n : ℕ, ∀ ρ : QMatrix (Fin n × I), ρ.PosSemidef → (amplify Φ ρ).PosSemidef

structure CPTP (I O : Type*) [Fintype I] [Fintype O] where
  map : QMatrix I →ₗ[ℂ] QMatrix O
  completelyPositive : IsCompletelyPositive map
  tracePreserving : ∀ ρ : QMatrix I, Matrix.trace (map ρ) = Matrix.trace ρ

namespace CPTP

variable {I O : Type*} [Fintype I] [Fintype O]

def identity (I : Type*) [Fintype I] : CPTP I I where
  map := LinearMap.id
  completelyPositive := by
    intro n ρ hρ
    have heq : QuantumProver.DepolarizingSquashedEntanglement.amplify (LinearMap.id : QMatrix I →ₗ[ℂ] QMatrix I) ρ =
        ρ := by
      ext i j
      rfl
    rw [heq]
    exact hρ
  tracePreserving := by intro ρ; rfl

theorem apply_positive (Φ : CPTP I O) {ρ : QMatrix I} (hρ : ρ.PosSemidef) :
    (Φ.map ρ).PosSemidef := by
  let σ : QMatrix (Fin 1 × I) := fun x y => ρ x.2 y.2
  have hσ : σ.PosSemidef := hρ.submatrix Prod.snd
  have h := Φ.completelyPositive 1 σ hσ
  have hsub := h.submatrix (fun i : O => ((0 : Fin 1), i))
  have heq : (QuantumProver.DepolarizingSquashedEntanglement.amplify Φ.map σ).submatrix
      (fun i : O => ((0 : Fin 1), i)) (fun i : O => ((0 : Fin 1), i)) = Φ.map ρ := by
    ext i j
    rfl
  rw [heq] at hsub
  exact hsub

def onDensity [DecidableEq I] [DecidableEq O] (Φ : CPTP I O) (ρ : Density I) :
    Density O where
  matrix := Φ.map ρ.matrix
  positive := Φ.apply_positive ρ.positive
  trace_one := (Φ.tracePreserving ρ.matrix).trans ρ.trace_one

end CPTP

structure KrausFamily (I O : Type*) [Fintype O] [DecidableEq I] where
  count : ℕ
  operator : Fin count → Matrix O I ℂ
  complete : ∑ k, (operator k).conjTranspose * operator k = 1

namespace KrausFamily

variable {I O : Type*} [Fintype I] [Fintype O] [DecidableEq I]

def apply (K : KrausFamily I O) (ρ : QMatrix I) : QMatrix O :=
  ∑ k, K.operator k * ρ * (K.operator k).conjTranspose

def toLinearMap (K : KrausFamily I O) : QMatrix I →ₗ[ℂ] QMatrix O where
  toFun := K.apply
  map_add' := by
    intro A B
    simp [apply, Matrix.mul_add, Matrix.add_mul, Finset.sum_add_distrib]
  map_smul' := by
    intro c A
    simp [apply, Matrix.mul_smul, Matrix.smul_mul, Finset.smul_sum]

theorem trace_apply (K : KrausFamily I O) (ρ : QMatrix I) :
    Matrix.trace (K.apply ρ) = Matrix.trace ρ := by
  calc
    _ = ∑ k, (K.operator k * ρ * (K.operator k).conjTranspose).trace :=
      Matrix.trace_sum _ _
    _ = ∑ k, ((K.operator k).conjTranspose * K.operator k * ρ).trace := by
      apply Finset.sum_congr rfl
      intro k _
      exact Matrix.trace_mul_cycle _ _ _
    _ = ((∑ k, (K.operator k).conjTranspose * K.operator k) * ρ).trace := by
      rw [Matrix.sum_mul, Matrix.trace_sum]
    _ = ρ.trace := by rw [K.complete, Matrix.one_mul]

theorem apply_positive (K : KrausFamily I O) {ρ : QMatrix I} (hρ : ρ.PosSemidef) :
    (K.apply ρ).PosSemidef := by
  unfold apply
  exact Matrix.posSemidef_sum Finset.univ
    (fun k _ => hρ.mul_mul_conjTranspose_same (K.operator k))

end KrausFamily

def pauli (j : CanonicalEnvironment) : QMatrix Qubit :=
  if j = 0 then 1 else if j = 1 then !![0, 1; 1, 0] else
    if j = 2 then !![0, -Complex.I; Complex.I, 0] else !![1, 0; 0, -1]

def pauliWeight (p : ℝ) (j : CanonicalEnvironment) : ℝ :=
  if j = 0 then 1 - 3 * p / 4 else p / 4

def canonicalIsometry (p : ℝ) : Matrix (Qubit × CanonicalEnvironment) Qubit ℂ :=
  fun x y => ((Real.sqrt (pauliWeight p x.2) : ℝ) : ℂ) * pauli x.2 x.1 y

def depolarizing (p : ℝ) (ρ : QMatrix Qubit) : QMatrix Qubit :=
  ((1 - p : ℝ) : ℂ) • ρ + (((p / 2 : ℝ) : ℂ) * Matrix.trace ρ) • 1

def extendedInputKet {R : Type*} [Fintype Qubit] (p : ℝ)
    (ψ : (R × Qubit) → ℂ) : ((R × Qubit) × CanonicalEnvironment) → ℂ :=
  fun x => ∑ i, canonicalIsometry p (x.1.2, x.2) i * ψ (x.1.1, i)

def postSquashing {R : Type*} [Fintype R] (p : ℝ)
    (ψ : (R × Qubit) → ℂ) {E : Type*} [Fintype E]
    (S : CPTP CanonicalEnvironment E) : QMatrix ((R × Qubit) × E) :=
  amplify S.map (pureDensity (extendedInputKet p ψ))

def inputCosts (p : ℝ) {r : ℕ} (ψ : (Fin r × Qubit) → ℂ) : Set ℝ :=
  {x | ∃ e : ℕ, ∃ S : CPTP CanonicalEnvironment (Fin e),
    x = cmiBits (postSquashing p ψ S)}

def squashedInputValue (p : ℝ) {r : ℕ} (ψ : (Fin r × Qubit) → ℂ) : ℝ :=
  (1 / 2 : ℝ) * sInf (inputCosts p ψ)

def channelInputValues (p : ℝ) : Set ℝ :=
  {x | ∃ r : ℕ, ∃ ψ : (Fin r × Qubit) → ℂ,
    IsNormalized ψ ∧ x = squashedInputValue p ψ}

def channelSquashed (p : ℝ) : ℝ := sSup (channelInputValues p)

def lowNoiseProfile (p : ℝ) : ℝ :=
  1 - (3 * p / 8) * (Real.log (1 / p) / Real.log 2)

def boundaryMixing (δ : ℝ) : ℝ := 2 / 3 - 4 * δ / 3

def IsSeparable {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (ρ : QMatrix (A × B)) : Prop :=
  ρ ∈ convexHull ℝ {τ : QMatrix (A × B) |
    ∃ a : Density A, ∃ b : Density B, τ = a.matrix ⊗ₖ b.matrix}

structure OneWayPOVM (A B X Y : Type*) [Fintype A] [Fintype B]
    [Fintype X] [Fintype Y] [DecidableEq A] [DecidableEq B] where
  alice : X → QMatrix A
  alice_positive : ∀ x, (alice x).PosSemidef
  alice_complete : ∑ x, alice x = 1
  bob : X → Y → QMatrix B
  bob_positive : ∀ x y, (bob x y).PosSemidef
  bob_complete : ∀ x, ∑ y, bob x y = 1

def oneWayOutcome {A B X Y : Type*} [Fintype A] [Fintype B]
    [Fintype X] [Fintype Y] [DecidableEq A] [DecidableEq B]
    (M : OneWayPOVM A B X Y) (ρ : QMatrix (A × B)) (x : X) (y : Y) : ℝ :=
  (Matrix.trace (ρ * (M.alice x ⊗ₖ M.bob x y))).re

def oneWayNorm {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (X : QMatrix (A × B)) : ℝ :=
  sSup {v : ℝ | ∃ m n : ℕ, ∃ M : OneWayPOVM A B (Fin m) (Fin n),
    v = ∑ x, ∑ y, |oneWayOutcome M X x y|}

end QuantumProver.DepolarizingSquashedEntanglement
