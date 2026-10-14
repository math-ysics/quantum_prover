import Mathlib

set_option autoImplicit false

noncomputable section

open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder Matrix Kronecker

namespace QuantumProver.AmplitudeDamping.FiniteModel

abbrev Qubit := Fin 2
abbrev BipartiteMatrix (a b : ℕ) :=
  Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ

def IsDensity {I : Type*} [Fintype I] (ρ : Matrix I I ℂ) : Prop :=
  ρ.PosSemidef ∧ ρ.trace = 1

structure KrausInstrument (i o k : ℕ) where
  operator : Fin k → Matrix (Fin o) (Fin i) ℂ
  complete : ∑ z, (operator z)ᴴ * operator z = 1

def dampingNoLoss (p : ℝ) : Matrix Qubit Qubit ℂ :=
  !![1, 0; 0, (Real.sqrt (1 - p) : ℂ)]

def dampingLoss (p : ℝ) : Matrix Qubit Qubit ℂ :=
  !![0, (Real.sqrt p : ℂ); 0, 0]

def dampingKraus (p : ℝ) (z : Qubit) : Matrix Qubit Qubit ℂ :=
  if z = 0 then dampingNoLoss p else dampingLoss p

def dampingOutput (p : ℝ) (ρ : Matrix Qubit Qubit ℂ) :
    Matrix Qubit Qubit ℂ :=
  dampingNoLoss p * ρ * (dampingNoLoss p)ᴴ +
    dampingLoss p * ρ * (dampingLoss p)ᴴ

def aliceOperator {a ao b : ℕ} (K : Matrix (Fin ao) (Fin a) ℂ) :
    Matrix (Fin ao × Fin b) (Fin a × Fin b) ℂ :=
  K ⊗ₖ (1 : Matrix (Fin b) (Fin b) ℂ)

def bobOperator {a b bo : ℕ} (K : Matrix (Fin bo) (Fin b) ℂ) :
    Matrix (Fin a × Fin bo) (Fin a × Fin b) ℂ :=
  (1 : Matrix (Fin a) (Fin a) ℂ) ⊗ₖ K

def splitQubit (a : ℕ) : Fin (2 * a) ≃ Qubit × Fin a :=
  (finProdFinEquiv : Qubit × Fin a ≃ Fin (2 * a)).symm

def callInputEquiv (a b : ℕ) :
    (Fin (2 * a) × Fin b) ≃ ((Fin a × Fin b) × Qubit) where
  toFun y := (((splitQubit a y.1).2, y.2), (splitQubit a y.1).1)
  invFun t := ((splitQubit a).symm (t.2, t.1.1), t.1.2)
  left_inv y := by simp
  right_inv t := by simp

def callOutputEquiv (a b : ℕ) :
    (Fin a × Fin (2 * b)) ≃ ((Fin a × Fin b) × Qubit) where
  toFun x := ((x.1, (splitQubit b x.2).2), (splitQubit b x.2).1)
  invFun t := (t.1.1, (splitQubit b).symm (t.2, t.1.2))
  left_inv x := by simp
  right_inv t := by simp

def callOperator (p : ℝ) (a b : ℕ) (z : Qubit) :
    Matrix (Fin a × Fin (2 * b)) (Fin (2 * a) × Fin b) ℂ :=
  fun x y =>
    dampingKraus p z (splitQubit b x.2).1 (splitQubit a y.1).1 *
      if x.1 = (splitQubit a y.1).2 ∧ (splitQubit b x.2).2 = y.2
      then 1 else 0

inductive FiniteProtocol (p : ℝ) : ℕ → ℕ → ℕ → ℕ → Type
  | done (a b : ℕ) : FiniteProtocol p a b a b
  | alice {a b ao af bf k : ℕ} (K : KrausInstrument a ao k)
      (next : Fin k → FiniteProtocol p ao b af bf) :
      FiniteProtocol p a b af bf
  | bob {a b bo af bf k : ℕ} (K : KrausInstrument b bo k)
      (next : Fin k → FiniteProtocol p a bo af bf) :
      FiniteProtocol p a b af bf
  | call {a b af bf : ℕ} (next : FiniteProtocol p a (2 * b) af bf) :
      FiniteProtocol p (2 * a) b af bf

def FiniteProtocol.calls {p : ℝ} {a b af bf : ℕ}
    (P : FiniteProtocol p a b af bf) : ℕ :=
  match P with
  | .done _ _ => 0
  | .alice _ next => Finset.univ.sup fun z => (next z).calls
  | .bob _ next => Finset.univ.sup fun z => (next z).calls
  | .call next => next.calls + 1

def FiniteProtocol.output {p : ℝ} {a b af bf : ℕ}
    (P : FiniteProtocol p a b af bf) (ρ : BipartiteMatrix a b) :
    BipartiteMatrix af bf :=
  match P with
  | .done _ _ => ρ
  | .alice K next => ∑ z, (next z).output
      (aliceOperator (b := b) (K.operator z) * ρ *
        (aliceOperator (b := b) (K.operator z))ᴴ)
  | .bob K next => ∑ z, (next z).output
      (bobOperator (a := a) (K.operator z) * ρ *
        (bobOperator (a := a) (K.operator z))ᴴ)
  | .call (a := a₀) (b := b₀) next =>
      next.output (∑ z : Qubit, callOperator p a₀ b₀ z * ρ *
        (callOperator p a₀ b₀ z)ᴴ)

@[simp] theorem FiniteProtocol.output_zero {p : ℝ} {a b af bf : ℕ}
    (P : FiniteProtocol p a b af bf) : P.output 0 = 0 := by
  induction P with
  | done a b => rfl
  | alice K next ih =>
      simp only [FiniteProtocol.output, Matrix.mul_zero, Matrix.zero_mul, ih,
        Finset.sum_const_zero]
  | bob K next ih =>
      simp only [FiniteProtocol.output, Matrix.mul_zero, Matrix.zero_mul, ih,
        Finset.sum_const_zero]
  | call next ih =>
      simp only [FiniteProtocol.output, Matrix.mul_zero, Matrix.zero_mul,
        Finset.sum_const_zero, ih]

def bellProjector (d : ℕ) : BipartiteMatrix d d :=
  fun x y => if x.1 = x.2 ∧ y.1 = y.2 then (1 / (d : ℂ)) else 0

def bellVector (d : ℕ) : Fin d × Fin d → ℂ :=
  fun x => if x.1 = x.2 then 1 / (Real.sqrt (d : ℝ) : ℂ) else 0

def bellOverlap (d : ℕ) (ρ : BipartiteMatrix d d) : ℝ :=
  (Matrix.trace (bellProjector d * ρ)).re

def IsSeparable (a b : ℕ) (ρ : BipartiteMatrix a b) : Prop :=
  ∃ (k : ℕ) (t : Fin k → ℝ)
      (A : Fin k → Matrix (Fin a) (Fin a) ℂ)
      (B : Fin k → Matrix (Fin b) (Fin b) ℂ),
    (∀ z, 0 ≤ t z) ∧ (∑ z, t z = 1) ∧
    (∀ z, IsDensity (A z) ∧ IsDensity (B z)) ∧
    ρ = ∑ z, (t z : ℂ) • (A z ⊗ₖ B z)

def SupportLE {I : Type*} [Fintype I] [DecidableEq I]
    (ρ σ : Matrix I I ℂ) : Prop :=
  LinearMap.range ρ.mulVecLin ≤ LinearMap.range σ.mulVecLin

def sandwichedTrace {I : Type*} [Fintype I] [DecidableEq I]
    (α : ℝ) (ρ σ : Matrix I I ℂ) : ℝ :=
  let W := CFC.rpow σ ((1 - α) / (2 * α))
  (CFC.rpow (W * ρ * W) α).trace.re

def sandwichedDivergence {I : Type*} [Fintype I] [DecidableEq I]
    (α : ℝ) (ρ σ : Matrix I I ℂ) : EReal := by
  classical
  exact if SupportLE ρ σ then
    ((Real.log (sandwichedTrace α ρ σ) / ((α - 1) * Real.log 2) : ℝ) : EReal)
  else ⊤

def sandwichedEntanglement (α : ℝ) (a b : ℕ) (ρ : BipartiteMatrix a b) : EReal :=
  sInf (sandwichedDivergence α ρ ''
    {σ : BipartiteMatrix a b | IsDensity σ ∧ IsSeparable a b σ})

def logTwo (x : ℝ) : ℝ := Real.log x / Real.log 2

def converseBudget (p s : ℝ) : ℝ :=
  if p = 0 then 1 else if p = 1 then 0 else if s = 1 then logTwo (2 - p)
  else logTwo (1 + ((1 - p) / (1 - p ^ (1 / (1 - s))) ^ (1 - s)) ^ (1 / s))

def bellConverseBound (p s : ℝ) (m d : ℕ) (e : ℝ) : ℝ :=
  min 1 (2 ^ (-(s / (1 + s)) *
    (logTwo (d : ℝ) - e - (m : ℝ) * converseBudget p s)))

def attainableOutputs (p s : ℝ) (m d : ℕ) (e : ℝ) : Set (BipartiteMatrix d d) :=
  {σ | ∃ (a b : ℕ) (ρ : BipartiteMatrix a b)
      (P : FiniteProtocol p a b d d),
    IsDensity ρ ∧ P.calls ≤ m ∧
    sandwichedEntanglement (1 + s) a b ρ ≤ (e : EReal) ∧ P.output ρ = σ}

def FiniteAdaptiveStrongConverse : Prop :=
  ∀ (p s : ℝ) (m d : ℕ) (e : ℝ),
    0 ≤ p → p ≤ 1 → 0 < s → s ≤ 1 → 2 ≤ d →
    ∀ σ ∈ closure (attainableOutputs p s m d e),
      bellOverlap d σ ≤ bellConverseBound p s m d e

end QuantumProver.AmplitudeDamping.FiniteModel
