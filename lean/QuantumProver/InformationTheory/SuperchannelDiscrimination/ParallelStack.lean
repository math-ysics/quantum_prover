import QuantumProver.InformationTheory.SuperchannelDiscrimination.StrategyAssembly
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option maxRecDepth 4000
noncomputable section

namespace QuantumProver.SuperchannelDiscrimination.MatrixStrategyAssembly.MatrixStrategies

open KrausCompletion CPWrappers
open scoped ComplexOrder MatrixOrder Matrix Kronecker

def unitFront (X : FiniteSystem) : X.basis ≃ (FiniteSystem.unit.prod X).basis where
  toFun x := ((), x)
  invFun x := x.2
  left_inv _ := rfl
  right_inv x := by rcases x with ⟨u, x⟩; cases u; rfl

def publicReindex {X Y U V : FiniteSystem}
    (eIn : U.basis ≃ X.basis) (eOut : Y.basis ≃ V.basis) :
    FiniteSuperchannel X.basis Y.basis U.basis V.basis FiniteSystem.unit.basis where
  pre := reindexChannel (eIn.trans (unitFront X))
  post := reindexChannel ((unitFront Y).symm.trans eOut)

theorem publicReindex_applyLinear {X Y U V : FiniteSystem}
    (eIn : U.basis ≃ X.basis) (eOut : Y.basis ≃ V.basis)
    (Φ : Matrix X.basis X.basis ℂ →ₗ[ℂ] Matrix Y.basis Y.basis ℂ)
    (A : Matrix U.basis U.basis ℂ) :
    (publicReindex (X := X) (Y := Y) (U := U) (V := V) eIn eOut).applyLinear Φ A =
      reindexMap eOut (Φ (reindexMap eIn A)) := by
  ext v w
  rfl

def NestedCircuit.relabel {I O C D X Y U V : FiniteSystem} {n : ℕ}
    (eIn : U.basis ≃ X.basis) (eOut : Y.basis ≃ V.basis)
    (inner : NestedCircuit I O C D X Y n) : NestedCircuit I O C D U V n :=
  .knownWrap (M := FiniteSystem.unit)
    (publicReindex (X := X) (Y := Y) (U := U) (V := V) eIn eOut) inner

theorem NestedCircuit.evaluate_relabel {I O C D R X Y U V : FiniteSystem} {n : ℕ}
    (Θ : FiniteSuperchannel I.basis O.basis C.basis D.basis R.basis)
    (eIn : U.basis ≃ X.basis) (eOut : Y.basis ≃ V.basis)
    (inner : NestedCircuit I O C D X Y n)
    (A : Matrix U.basis U.basis ℂ) :
    ((inner.relabel eIn eOut).evaluate Θ).map A =
      reindexMap eOut ((inner.evaluate Θ).map (reindexMap eIn A)) :=
  publicReindex_applyLinear (X := X) (Y := Y) (U := U) (V := V)
    eIn eOut (inner.evaluate Θ).map A

def frontTailSwap (A B X : FiniteSystem) :
    ((A.prod B).prod X).basis ≃ (B.prod (A.prod X)).basis where
  toFun x := (x.1.2, (x.1.1, x.2))
  invFun x := ((x.2.1, x.1), x.2.2)
  left_inv x := by rcases x with ⟨⟨a, b⟩, x⟩; rfl
  right_inv x := by rcases x with ⟨b, ⟨a, x⟩⟩; rfl

def middleSwap (A B X : FiniteSystem) :
    (A.prod (B.prod X)).basis ≃ (B.prod (A.prod X)).basis where
  toFun x := (x.2.1, (x.1, x.2.2))
  invFun x := (x.2.1, (x.1, x.2.2))
  left_inv x := by rcases x with ⟨a, ⟨b, x⟩⟩; rfl
  right_inv x := by rcases x with ⟨b, ⟨a, x⟩⟩; rfl

def tailFirstKnown (I O : FiniteSystem) (n : ℕ) (X Y : FiniteSystem)
    (K : FiniteCPTP ((I.tensorPower (n + 1)).prod X).basis
      ((O.tensorPower (n + 1)).prod Y).basis) :
    FiniteCPTP ((I.tensorPower n).prod (I.prod X)).basis
      ((O.tensorPower n).prod (O.prod Y)).basis :=
  composeChannel (reindexChannel (frontTailSwap O (O.tensorPower n) Y))
    (composeChannel K (reindexChannel (frontTailSwap I (I.tensorPower n) X).symm))

def parallelStackCircuit (I O C D : FiniteSystem) :
    (n : ℕ) → (X Y : FiniteSystem) →
    FiniteCPTP ((I.tensorPower n).prod X).basis ((O.tensorPower n).prod Y).basis →
    NestedCircuit I O C D ((C.tensorPower n).prod X) ((D.tensorPower n).prod Y) n
  | 0, _, _, K => .known K
  | n + 1, X, Y, K =>
      let tail := parallelStackCircuit I O C D n (I.prod X) (O.prod Y)
        (tailFirstKnown I O n X Y K)
      let reordered : NestedCircuit I O C D
          (I.prod ((C.tensorPower n).prod X)) (O.prod ((D.tensorPower n).prod Y)) n := tail.relabel
        (U := I.prod ((C.tensorPower n).prod X))
        (V := O.prod ((D.tensorPower n).prod Y))
        (middleSwap I (C.tensorPower n) X)
        (middleSwap O (D.tensorPower n) Y).symm
      let used : NestedCircuit I O C D
          (C.prod ((C.tensorPower n).prod X)) (D.prod ((D.tensorPower n).prod Y)) (n + 1) := NestedCircuit.testedUse
        (X := (C.tensorPower n).prod X) (Y := (D.tensorPower n).prod Y) reordered
      used.relabel
        (X := C.prod ((C.tensorPower n).prod X))
        (Y := D.prod ((D.tensorPower n).prod Y))
        (U := (C.tensorPower (n + 1)).prod X)
        (V := (D.tensorPower (n + 1)).prod Y)
        (Equiv.prodAssoc C.basis (C.tensorPower n).basis X.basis)
        (Equiv.prodAssoc D.basis (D.tensorPower n).basis Y.basis).symm

theorem parallelStackCircuit_evaluate_zero {I O C D R : FiniteSystem}
    (Θ : FiniteSuperchannel I.basis O.basis C.basis D.basis R.basis)
    (X Y : FiniteSystem)
    (K : FiniteCPTP ((I.tensorPower 0).prod X).basis ((O.tensorPower 0).prod Y).basis) :
    (parallelStackCircuit I O C D 0 X Y K).evaluate Θ = K := rfl

theorem parallelStackCircuit_evaluate_succ {I O C D R : FiniteSystem}
    (Θ : FiniteSuperchannel I.basis O.basis C.basis D.basis R.basis)
    (n : ℕ) (X Y : FiniteSystem)
    (K : FiniteCPTP ((I.tensorPower (n + 1)).prod X).basis
      ((O.tensorPower (n + 1)).prod Y).basis) :
    (parallelStackCircuit I O C D (n + 1) X Y K).evaluate Θ =
      (publicReindex
        (X := C.prod ((C.tensorPower n).prod X))
        (Y := D.prod ((D.tensorPower n).prod Y))
        (U := (C.tensorPower (n + 1)).prod X)
        (V := (D.tensorPower (n + 1)).prod Y)
        (Equiv.prodAssoc C.basis (C.tensorPower n).basis X.basis)
        (Equiv.prodAssoc D.basis (D.tensorPower n).basis Y.basis).symm).applyChannel
      ((extendSidePorts Θ ((C.tensorPower n).prod X) ((D.tensorPower n).prod Y)).applyChannel
      ((publicReindex
        (X := (C.tensorPower n).prod (I.prod X))
        (Y := (D.tensorPower n).prod (O.prod Y))
        (U := I.prod ((C.tensorPower n).prod X))
        (V := O.prod ((D.tensorPower n).prod Y))
        (middleSwap I (C.tensorPower n) X)
        (middleSwap O (D.tensorPower n) Y).symm).applyChannel
      ((parallelStackCircuit I O C D n (I.prod X) (O.prod Y)
        (tailFirstKnown I O n X Y K)).evaluate Θ))) := rfl

theorem parallelStackCircuit_density {I O C D R : FiniteSystem}
    (Θ : FiniteSuperchannel I.basis O.basis C.basis D.basis R.basis)
    (n : ℕ) (X Y : FiniteSystem)
    (K : FiniteCPTP ((I.tensorPower n).prod X).basis ((O.tensorPower n).prod Y).basis)
    {ρ : Matrix ((C.tensorPower n).prod X).basis ((C.tensorPower n).prod X).basis ℂ}
    (hρ : FlaggedStates.IsDensity ρ) :
    FlaggedStates.IsDensity (((parallelStackCircuit I O C D n X Y K).evaluate Θ).map ρ) :=
  NestedCircuit.evaluate_density Θ _ hρ

end QuantumProver.SuperchannelDiscrimination.MatrixStrategyAssembly.MatrixStrategies

namespace QuantumProver.SuperchannelDiscrimination.MatrixStrategyAssembly.MatrixStrategies

open KrausCompletion CPWrappers
open scoped ComplexOrder MatrixOrder Matrix Kronecker

def productStackChannel {I O C D R I' O' C' D' R' : FiniteSystem}
    (Θ : FiniteSuperchannel I.basis O.basis C.basis D.basis R.basis)
    (Ψ : FiniteSuperchannel I'.basis O'.basis C'.basis D'.basis R'.basis)
    (X Y : FiniteSystem)
    (K : FiniteCPTP ((I.prod I').prod X).basis ((O.prod O').prod Y).basis) :
    FiniteCPTP ((C.prod C').prod X).basis ((D.prod D').prod Y).basis :=
  let tailKnown : FiniteCPTP (I'.prod (I.prod X)).basis (O'.prod (O.prod Y)).basis :=
    composeChannel (reindexChannel (frontTailSwap O O' Y))
      (composeChannel K (reindexChannel (frontTailSwap I I' X).symm))
  let tail := (extendSidePorts Ψ (I.prod X) (O.prod Y)).applyChannel tailKnown
  let reordered := (publicReindex
    (X := C'.prod (I.prod X)) (Y := D'.prod (O.prod Y))
    (U := I.prod (C'.prod X)) (V := O.prod (D'.prod Y))
    (middleSwap I C' X) (middleSwap O D' Y).symm).applyChannel tail
  let used := (extendSidePorts Θ (C'.prod X) (D'.prod Y)).applyChannel reordered
  (publicReindex
    (X := C.prod (C'.prod X)) (Y := D.prod (D'.prod Y))
    (U := (C.prod C').prod X) (V := (D.prod D').prod Y)
    (Equiv.prodAssoc C.basis C'.basis X.basis)
    (Equiv.prodAssoc D.basis D'.basis Y.basis).symm).applyChannel used

theorem productStackChannel_map {I O C D R I' O' C' D' R' : FiniteSystem}
    (Θ : FiniteSuperchannel I.basis O.basis C.basis D.basis R.basis)
    (Ψ : FiniteSuperchannel I'.basis O'.basis C'.basis D'.basis R'.basis)
    (X Y : FiniteSystem)
    (K : FiniteCPTP ((I.prod I').prod X).basis ((O.prod O').prod Y).basis) :
    (productStackChannel Θ Ψ X Y K).map =
      ((extendSidePorts (productSuperchannel Θ Ψ) X Y).applyChannel K).map := by
  have hpost : (productChannel Θ.post Ψ.post).map =
      (amplifyMap Θ.post.map D'.basis).comp
        (amplifyLeftMap Ψ.post.map (R.prod O).basis) :=
    disjoint_factor_maps_commute Θ.post.map Ψ.post.map
  apply LinearMap.ext
  intro A
  simp only [productStackChannel, FiniteSuperchannel.applyChannel_map,
    publicReindex_applyLinear]
  simp only [extendSidePorts, productSuperchannel, FiniteSuperchannel.applyLinear,
    composeChannel, LinearMap.comp_apply]
  simp only [amplifiedChannel, reindexChannel, publicReindex,
    composeChannel, LinearMap.comp_apply]
  rw [hpost]
  ext ⟨⟨d, d'⟩, y⟩ ⟨⟨e, e'⟩, y'⟩
  rfl

end QuantumProver.SuperchannelDiscrimination.MatrixStrategyAssembly.MatrixStrategies

namespace QuantumProver.SuperchannelDiscrimination.MatrixStrategyAssembly.MatrixStrategies

open KrausCompletion CPWrappers FlaggedStates
open scoped ComplexOrder MatrixOrder Matrix Kronecker

theorem parallelChannel_zero_map {I O C D R : FiniteSystem}
    (Θ : FiniteSuperchannel I.basis O.basis C.basis D.basis R.basis)
    (X Y : FiniteSystem)
    (K : FiniteCPTP ((I.tensorPower 0).prod X).basis ((O.tensorPower 0).prod Y).basis) :
    (parallelChannel Θ 0 X Y K).map = K.map := by
  apply LinearMap.ext
  intro A
  ext ⟨⟨⟩, y⟩ ⟨⟨⟩, y'⟩
  change K.map (fun x z => A ((), x.2) ((), z.2)) ((), y) ((), y') =
    K.map A ((), y) ((), y')
  congr 1

theorem parallelStackCircuit_map {I O C D R : FiniteSystem}
    (Θ : FiniteSuperchannel I.basis O.basis C.basis D.basis R.basis)
    (n : ℕ) (X Y : FiniteSystem)
    (K : FiniteCPTP ((I.tensorPower n).prod X).basis ((O.tensorPower n).prod Y).basis) :
    ((parallelStackCircuit I O C D n X Y K).evaluate Θ).map =
      (parallelChannel Θ n X Y K).map := by
  induction n generalizing X Y with
  | zero =>
      change K.map = (parallelChannel Θ 0 X Y K).map
      exact (parallelChannel_zero_map Θ X Y K).symm
  | succ n ih =>
      rw [parallelStackCircuit_evaluate_succ]
      simp only [FiniteSuperchannel.applyChannel_map]
      rw [ih]
      change (productStackChannel Θ (parallelPower Θ n) X Y K).map =
        ((extendSidePorts (productSuperchannel Θ (parallelPower Θ n)) X Y).applyChannel K).map
      exact productStackChannel_map Θ (parallelPower Θ n) X Y K

private theorem binaryTest_eq_of_errors {S T : BinaryTest}
    (ha : S.alpha = T.alpha) (hb : S.beta = T.beta) : S = T := by
  cases S
  cases T
  simp_all

theorem parallelStackCircuit_binaryTest {I O C D R₁ R₂ : FiniteSystem}
    (Θ₁ : FiniteSuperchannel I.basis O.basis C.basis D.basis R₁.basis)
    (Θ₂ : FiniteSuperchannel I.basis O.basis C.basis D.basis R₂.basis)
    (n : ℕ) (X Y : FiniteSystem)
    (K : FiniteCPTP ((I.tensorPower n).prod X).basis ((O.tensorPower n).prod Y).basis)
    (ρ : Matrix ((C.tensorPower n).prod X).basis ((C.tensorPower n).prod X).basis ℂ)
    (E : Matrix ((D.tensorPower n).prod Y).basis ((D.tensorPower n).prod Y).basis ℂ)
    (hρ : IsDensity ρ) (hE : IsEffect E) :
    (parallelStackCircuit I O C D n X Y K).binaryTest Θ₁ Θ₂ ρ E hρ hE =
      parallelBinaryTest Θ₁ Θ₂ n X Y K ρ E hρ hE := by
  apply binaryTest_eq_of_errors
  · change 1 - acceptanceProbability
      (((parallelStackCircuit I O C D n X Y K).evaluate Θ₁).map ρ) E =
        1 - acceptanceProbability ((parallelChannel Θ₁ n X Y K).map ρ) E
    rw [parallelStackCircuit_map]
  · change acceptanceProbability
      (((parallelStackCircuit I O C D n X Y K).evaluate Θ₂).map ρ) E =
        acceptanceProbability ((parallelChannel Θ₂ n X Y K).map ρ) E
    rw [parallelStackCircuit_map]

theorem parallelStrategyFamily_subset_nested {I O C D R₁ R₂ : FiniteSystem}
    (Θ₁ : FiniteSuperchannel I.basis O.basis C.basis D.basis R₁.basis)
    (Θ₂ : FiniteSuperchannel I.basis O.basis C.basis D.basis R₂.basis) :
    ∀ n, parallelStrategyFamily Θ₁ Θ₂ n ⊆ nestedStrategyFamily Θ₁ Θ₂ n := by
  intro n T hT
  rcases hT with ⟨X, Y, K, ρ, E, hρ, hE, rfl⟩
  refine ⟨(C.tensorPower n).prod X, (D.tensorPower n).prod Y,
    parallelStackCircuit I O C D n X Y K, ρ, E, hρ, hE, ?_⟩
  exact (parallelStackCircuit_binaryTest Θ₁ Θ₂ n X Y K ρ E hρ hE).symm

theorem matrix_parallel_optimalBeta_ge_nested {I O C D R₁ R₂ : FiniteSystem}
    (Θ₁ : FiniteSuperchannel I.basis O.basis C.basis D.basis R₁.basis)
    (Θ₂ : FiniteSuperchannel I.basis O.basis C.basis D.basis R₂.basis)
    (ε : ℝ) (n : ℕ) :
    optimalBeta (nestedStrategyFamily Θ₁ Θ₂) ε n ≤
      optimalBeta (parallelStrategyFamily Θ₁ Θ₂) ε n :=
  optimalBeta_antitone_family (parallelStrategyFamily_subset_nested Θ₁ Θ₂) ε n

theorem matrix_parallel_orderedSteinExponent_le_nested {I O C D R₁ R₂ : FiniteSystem}
    (Θ₁ : FiniteSuperchannel I.basis O.basis C.basis D.basis R₁.basis)
    (Θ₂ : FiniteSuperchannel I.basis O.basis C.basis D.basis R₂.basis) :
    orderedSteinExponent (parallelStrategyFamily Θ₁ Θ₂) ≤
      orderedSteinExponent (nestedStrategyFamily Θ₁ Θ₂) :=
  orderedSteinExponent_mono_family (parallelStrategyFamily_subset_nested Θ₁ Θ₂)

end QuantumProver.SuperchannelDiscrimination.MatrixStrategyAssembly.MatrixStrategies
