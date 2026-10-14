import Mathlib

/-!
Definitions for the visible compression problem. These are operational
definitions, not assumptions of the proposed dimension bound. In particular,
the code has arbitrary label-dependent quantum message states and a genuine
completely positive trace-preserving decoder in every seed branch.

No support-score bound, Choi-purity inequality, entropy identity, or asymptotic
converse is included as a field of these structures.
-/

noncomputable section

open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace VisibleCompression

def log2 (x : ℝ) : ℝ := Real.log x / Real.log 2

def holevoD9 : ℝ := log2 (9 / 8)

def lowerRateD9 : ℝ := (2 / 3) * log2 (45 / 37)

def decayD9 : ℝ := 37 / 45

universe u v w

/-- A finite probability distribution; zero-weight seeds are allowed. -/
structure ProbWeights (X : Type u) [Fintype X] where
  weight : X → ℝ
  nonneg : ∀ x, 0 ≤ weight x
  normalized : ∑ x, weight x = 1

def ProbWeights.FullSupport {X : Type u} [Fintype X] (p : ProbWeights X) : Prop :=
  ∀ x, 0 < p.weight x

/-- Density operators are positive semidefinite matrices of complex trace one. -/
structure Density (B : Type v) [Fintype B] where
  mat : Matrix B B ℂ
  positive : mat.PosSemidef
  normalized : mat.trace = 1

/-- Apply a linear map to each input block of an ancillary matrix. -/
def amplify {I : Type u} {B : Type v} [Fintype I] [Fintype B]
    (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix B B ℂ) (k : ℕ)
    (A : Matrix (Fin k × I) (Fin k × I) ℂ) :
    Matrix (Fin k × B) (Fin k × B) ℂ :=
  fun i j => Φ (fun a b => A (i.1, a) (j.1, b)) i.2 j.2

/-- Complete positivity is required at every finite ancillary dimension. -/
structure CPTP (I : Type u) (B : Type v) [Fintype I] [Fintype B] where
  map : Matrix I I ℂ →ₗ[ℂ] Matrix B B ℂ
  completelyPositive : ∀ (k : ℕ)
    (A : Matrix (Fin k × I) (Fin k × I) ℂ),
    A.PosSemidef → (amplify map k A).PosSemidef
  tracePreserving : ∀ A, (map A).trace = A.trace

/-- A visible code for a finite block alphabet. The seed law is a function of
the seed alone, so it is independent of the source label. The common quantum
message dimension is `d`, not the cardinality of the seed or the decoder's
ancillary environment. -/
structure VisibleCode (X : Type u) (B : Type v) (S : Type w)
    [Fintype X] [Fintype B] [Fintype S] (d : ℕ) where
  messageDimension_pos : 0 < d
  seed : ProbWeights S
  encode : X → S → Density (Fin d)
  decode : S → CPTP (Fin d) B

namespace VisibleCode

variable {X : Type u} {B : Type v} {S : Type w}
  [Fintype X] [Fintype B] [Fintype S] {d : ℕ}

def branchOutput (C : VisibleCode X B S d) (x : X) (s : S) : Matrix B B ℂ :=
  (C.decode s).map (C.encode x s).mat

/-- The seed is averaged before any error norm is taken. -/
def reproduced (C : VisibleCode X B S d) (x : X) : Matrix B B ℂ :=
  ∑ s, (C.seed.weight s : ℂ) • C.branchOutput x s

end VisibleCode

/-- Nuclear/trace norm: `Tr sqrt(Aᴴ * A)`. The CFC absolute value is
definitionally `sqrt (star A * A)`; its trace is real because it is positive. -/
def traceNorm {B : Type v} [Fintype B] [DecidableEq B]
    (A : Matrix B B ℂ) : ℝ :=
  (CFC.abs A).trace.re

/-- Support-score evaluation does not give the source label to the decoder. -/
def supportScore {B : Type v} [Fintype B]
    (P ρ : Matrix B B ℂ) : ℝ := (P * ρ).trace.re

def averageSupportScore {X : Type u} {B : Type v}
    [Fintype X] [Fintype B] (p : ProbWeights X)
    (P ρ : X → Matrix B B ℂ) : ℝ :=
  ∑ x, p.weight x * supportScore (P x) (ρ x)

def blockError {X : Type u} {B : Type v} {S : Type w}
    [Fintype X] [Fintype B] [Fintype S] [DecidableEq B]
    {d : ℕ} (p : ProbWeights X) (target : X → Matrix B B ℂ)
    (C : VisibleCode X B S d) : ℝ :=
  (1 / 2) * ∑ x, p.weight x * traceNorm (target x - C.reproduced x)

/-- Fixed one-letter alphabet, iid block labels. -/
abbrev BlockLabels (X : Type u) (n : ℕ) := Fin n → X

/-- A basis of the full tensor-power output space, of dimension `D^n`. -/
abbrev BlockBasis (D n : ℕ) := Fin n → Fin D

def iidWeight {X : Type u} [Fintype X] (p : ProbWeights X) (n : ℕ)
    (x : BlockLabels X n) : ℝ := ∏ t, p.weight (x t)

/-- Tensor-product target matrix, with entries in the tensor-product basis. -/
def iidTarget {X : Type u} [Fintype X] {D : ℕ}
    (W : X → Density (Fin D)) (n : ℕ) (x : BlockLabels X n) :
    Matrix (BlockBasis D n) (BlockBasis D n) ℂ :=
  fun b c => ∏ t, (W (x t)).mat (b t) (c t)

/-- Every finite seed set can be relabeled as `Fin seedCard`; no bound on
`seedCard` is imposed and it can vary with block length. -/
structure BlockCode (X : Type u) [Fintype X] (D n : ℕ) where
  seedCard : ℕ
  messageDimension : ℕ
  code : VisibleCode (BlockLabels X n) (BlockBasis D n)
    (Fin seedCard) messageDimension

def iidBlockError {X : Type u} [Fintype X] {D : ℕ}
    (p : ProbWeights X) (W : X → Density (Fin D)) (n : ℕ)
    (C : BlockCode X D n) : ℝ :=
  (1 / 2) * ∑ x, iidWeight p n x *
    traceNorm (iidTarget W n x - C.code.reproduced x)

def blockRate {X : Type u} [Fintype X] {D n : ℕ}
    (C : BlockCode X D n) : ℝ := log2 C.messageDimension / (n : ℝ)

def VanishingError {X : Type u} [Fintype X] {D : ℕ}
    (p : ProbWeights X) (W : X → Density (Fin D))
    (C : ∀ n, BlockCode X D n) : Prop :=
  Filter.Tendsto (fun n => iidBlockError p W n (C n)) Filter.atTop (nhds 0)

/-- Extended-real limsup covers unbounded rate sequences. -/
def asymptoticRate {X : Type u} [Fintype X] {D : ℕ}
    (C : ∀ n, BlockCode X D n) : EReal :=
  Filter.limsup (fun n => (blockRate (C n) : EReal)) Filter.atTop

def visibleRate {X : Type u} [Fintype X] {D : ℕ}
    (p : ProbWeights X) (W : X → Density (Fin D)) : EReal :=
  sInf {r | ∃ C : ∀ n, BlockCode X D n,
    VanishingError p W C ∧ asymptoticRate C = r}

end VisibleCompression
