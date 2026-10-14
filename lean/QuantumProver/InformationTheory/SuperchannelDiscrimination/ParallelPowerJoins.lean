import QuantumProver.InformationTheory.SuperchannelDiscrimination.ParallelStack
import QuantumProver.InformationTheory.SuperchannelDiscrimination.CommonWrapperRegularization
import QuantumProver.InformationTheory.SuperchannelDiscrimination.TestingConsequences

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option maxRecDepth 4000
noncomputable section

namespace QuantumProver.SuperchannelDiscrimination.MatrixParallelPowerJoins

open Matrix KrausCompletion CPWrappers FlaggedStates TensorEntropy ChannelRegularization
open MatrixStrategyAssembly.MatrixStrategies
open scoped BigOperators ComplexOrder MatrixOrder Matrix Kronecker

def frontTailIndex (X : FiniteSystem) : (n : ℕ) →
    (X.tensorPower n).basis ≃ TensorIndex X.basis n
  | 0 =>
      { toFun := fun _ => PUnit.unit
        invFun := fun _ => ()
        left_inv := fun x => by cases x; rfl
        right_inv := fun x => by cases x; rfl }
  | n + 1 =>
      (Equiv.prodCongr (Equiv.refl X.basis) (frontTailIndex X n)).trans
        (Equiv.prodComm X.basis (TensorIndex X.basis n))

def matrixChannelPower {I O : FiniteSystem} (Φ : FiniteCPTP I.basis O.basis) :
    (n : ℕ) → FiniteCPTP (I.tensorPower n).basis (O.tensorPower n).basis
  | 0 => reindexChannel (Equiv.refl FiniteSystem.unit.basis)
  | n + 1 => productChannel Φ (matrixChannelPower Φ n)

def matrixUnitOutput {I O : FiniteSystem} (Φ : FiniteCPTP I.basis O.basis) :
    (n : ℕ) → (I.tensorPower n).basis → (I.tensorPower n).basis →
      Matrix (O.tensorPower n).basis (O.tensorPower n).basis ℂ
  | 0, _, _ => 1
  | n + 1, i, j => Φ.map (Matrix.single i.1 j.1 1) ⊗ₖ matrixUnitOutput Φ n i.2 j.2

theorem matrixChannelPower_map_single {I O : FiniteSystem}
    (Φ : FiniteCPTP I.basis O.basis) (n : ℕ)
    (i j : (I.tensorPower n).basis) :
    (matrixChannelPower Φ n).map (Matrix.single i j 1) = matrixUnitOutput Φ n i j := by
  induction n with
  | zero =>
      cases i
      cases j
      ext x y
      cases x
      cases y
      change (Matrix.single () () (1 : ℂ)) () () = (1 : ℂ)
      simp [Matrix.single_apply]
  | succ n ih =>
      rcases i with ⟨i, is⟩
      rcases j with ⟨j, js⟩
      have hs : Matrix.single (i, is) (j, js) (1 : ℂ) =
          Matrix.single i j 1 ⊗ₖ Matrix.single is js 1 := by
        rw [Matrix.single_kronecker_single, one_mul]
      change (productChannel Φ (matrixChannelPower Φ n)).map
        (Matrix.single (i, is) (j, js) 1) = _
      rw [hs, productChannel_kronecker, ih]
      rfl

theorem matrixUnitOutput_transport {I O : FiniteSystem}
    (Φ : FiniteCPTP I.basis O.basis) (n : ℕ)
    (i j : (I.tensorPower n).basis) :
    reindexMap (frontTailIndex O n) (matrixUnitOutput Φ n i j) =
      tensorUnitOutput Φ n (frontTailIndex I n i) (frontTailIndex I n j) := by
  induction n with
  | zero =>
      ext x y
      cases x
      cases y
      simp [matrixUnitOutput, tensorUnitOutput, reindexMap, Matrix.reindex_apply,
        Matrix.submatrix_apply]
  | succ n ih =>
      ext ⟨os, o⟩ ⟨ps, p⟩
      have h := congrArg (fun A : Matrix (TensorIndex O.basis n)
        (TensorIndex O.basis n) ℂ => A os ps) (ih i.2 j.2)
      change Φ.map (Matrix.single i.1 j.1 1) o p *
        matrixUnitOutput Φ n i.2 j.2 ((frontTailIndex O n).symm os)
          ((frontTailIndex O n).symm ps) =
        tensorUnitOutput Φ n (frontTailIndex I n i.2) (frontTailIndex I n j.2) os ps *
          Φ.map (Matrix.single i.1 j.1 1) o p
      change matrixUnitOutput Φ n i.2 j.2 ((frontTailIndex O n).symm os)
        ((frontTailIndex O n).symm ps) = _ at h
      rw [h, mul_comm]

theorem matrixChannelPower_intertwine {I O : FiniteSystem}
    (Φ : FiniteCPTP I.basis O.basis) (n : ℕ)
    (A : Matrix (I.tensorPower n).basis (I.tensorPower n).basis ℂ) :
    reindexMap (frontTailIndex O n) ((matrixChannelPower Φ n).map A) =
      (channelPower Φ n).map (reindexMap (frontTailIndex I n) A) := by
  have hm : (reindexMap (frontTailIndex O n)).comp (matrixChannelPower Φ n).map =
      (channelPower Φ n).map.comp (reindexMap (frontTailIndex I n)) := by
    apply matrixMap_ext_units
    intro i j
    simp only [LinearMap.comp_apply, matrixChannelPower_map_single, reindexMap_apply,
      reindex_single, channelPower_map_single]
    exact matrixUnitOutput_transport Φ n i j
  exact congrArg (fun F => F A) hm

theorem shuffled_amplify_product {I O R I' O' R' : FiniteSystem}
    (Φ : Matrix I.basis I.basis ℂ →ₗ[ℂ] Matrix O.basis O.basis ℂ)
    (Ψ : Matrix I'.basis I'.basis ℂ →ₗ[ℂ] Matrix O'.basis O'.basis ℂ) :
    (reindexMap (pairShuffle R.basis O.basis R'.basis O'.basis).symm).comp
      ((amplifyLeftMap (productLinear Φ Ψ) (R.basis × R'.basis)).comp
        (reindexMap (pairShuffle R.basis I.basis R'.basis I'.basis))) =
      productLinear (amplifyLeftMap Φ R.basis) (amplifyLeftMap Ψ R'.basis) := by
  apply LinearMap.ext
  intro A
  ext ⟨⟨r, o⟩, ⟨r', o'⟩⟩ ⟨⟨s, p⟩, ⟨s', p'⟩⟩
  rfl

theorem productSuperchannel_apply_product {I O C D R I' O' C' D' R' : FiniteSystem}
    (Θ : FiniteSuperchannel I.basis O.basis C.basis D.basis R.basis)
    (Ψ : FiniteSuperchannel I'.basis O'.basis C'.basis D'.basis R'.basis)
    (Φ : FiniteCPTP I.basis O.basis) (Φ' : FiniteCPTP I'.basis O'.basis) :
    ((productSuperchannel Θ Ψ).applyChannel (productChannel Φ Φ')).map =
      (productChannel (Θ.applyChannel Φ) (Ψ.applyChannel Φ')).map := by
  change (productLinear Θ.post.map Ψ.post.map).comp
      ((reindexMap (pairShuffle R.basis O.basis R'.basis O'.basis).symm).comp
        ((amplifyLeftMap (productLinear Φ.map Φ'.map) (R.basis × R'.basis)).comp
          ((reindexMap (pairShuffle R.basis I.basis R'.basis I'.basis)).comp
            (productLinear Θ.pre.map Ψ.pre.map)))) =
    productLinear (Θ.applyLinear Φ.map) (Ψ.applyLinear Φ'.map)
  have hs := shuffled_amplify_product (I := I) (O := O) (R := R)
    (I' := I') (O' := O') (R' := R') Φ.map Φ'.map
  have he := congrArg (fun F => (productLinear Θ.post.map Ψ.post.map).comp
    (F.comp (productLinear Θ.pre.map Ψ.pre.map))) hs
  simpa only [LinearMap.comp_assoc, ← productLinear_comp_matrix,
    FiniteSuperchannel.applyLinear] using he

def matrixTensorPower {X : FiniteSystem} (A : Matrix X.basis X.basis ℂ) :
    (n : ℕ) → Matrix (X.tensorPower n).basis (X.tensorPower n).basis ℂ
  | 0 => 1
  | n + 1 => A ⊗ₖ matrixTensorPower A n

theorem matrixTensorPower_transport {X : FiniteSystem}
    (A : Matrix X.basis X.basis ℂ) (n : ℕ) :
    reindexMap (frontTailIndex X n) (matrixTensorPower A n) = tensorPower A n := by
  induction n with
  | zero =>
      ext x y
      cases x
      cases y
      simp [matrixTensorPower, tensorPower, reindexMap, Matrix.reindex_apply,
        Matrix.submatrix_apply]
  | succ n ih =>
      ext ⟨xs, x⟩ ⟨ys, y⟩
      have h := congrArg (fun B : Matrix (TensorIndex X.basis n)
        (TensorIndex X.basis n) ℂ => B xs ys) ih
      change A x y * matrixTensorPower A n ((frontTailIndex X n).symm xs)
          ((frontTailIndex X n).symm ys) = tensorPower A n xs ys * A x y
      change matrixTensorPower A n ((frontTailIndex X n).symm xs)
        ((frontTailIndex X n).symm ys) = _ at h
      rw [h, mul_comm]

theorem matrixTensorPower_isDensity {X : FiniteSystem}
    {ρ : Matrix X.basis X.basis ℂ} (hρ : IsDensity ρ) (n : ℕ) :
    IsDensity (matrixTensorPower ρ n) := by
  induction n with
  | zero =>
      exact ⟨Matrix.PosSemidef.one, by
        simp [matrixTensorPower, Matrix.trace_one, FiniteSystem.tensorPower, FiniteSystem.unit]⟩
  | succ n ih => exact isDensity_kronecker hρ ih

theorem matrixChannelPower_tensor_output {I O : FiniteSystem}
    (Φ : FiniteCPTP I.basis O.basis) (A : Matrix I.basis I.basis ℂ) (n : ℕ) :
    (matrixChannelPower Φ n).map (matrixTensorPower A n) =
      matrixTensorPower (Φ.map A) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change (productChannel Φ (matrixChannelPower Φ n)).map
        (A ⊗ₖ matrixTensorPower A n) = Φ.map A ⊗ₖ matrixTensorPower (Φ.map A) n
      rw [productChannel_kronecker, ih]

theorem parallelPower_apply_matrixChannelPower {I O C D R : FiniteSystem}
    (Θ : FiniteSuperchannel I.basis O.basis C.basis D.basis R.basis)
    (Φ : FiniteCPTP I.basis O.basis) (n : ℕ) :
    ((parallelPower Θ n).applyChannel (matrixChannelPower Φ n)).map =
      (matrixChannelPower (Θ.applyChannel Φ) n).map := by
  induction n with
  | zero =>
      apply LinearMap.ext
      intro A
      ext x y
      cases x
      cases y
      rfl
  | succ n ih =>
      change ((productSuperchannel Θ (parallelPower Θ n)).applyChannel
        (productChannel Φ (matrixChannelPower Φ n))).map =
        (productChannel (Θ.applyChannel Φ) (matrixChannelPower (Θ.applyChannel Φ) n)).map
      rw [productSuperchannel_apply_product]
      change productLinear (Θ.applyChannel Φ).map
        (((parallelPower Θ n).applyChannel (matrixChannelPower Φ n)).map) =
        productLinear (Θ.applyChannel Φ).map (matrixChannelPower (Θ.applyChannel Φ) n).map
      rw [ih]

def matrixPowerPairIndex (X Y : FiniteSystem) : (n : ℕ) →
    ((X.prod Y).tensorPower n).basis ≃ ((X.tensorPower n).prod (Y.tensorPower n)).basis
  | 0 => unitPair
  | n + 1 =>
      (Equiv.prodCongr (Equiv.refl (X.prod Y).basis) (matrixPowerPairIndex X Y n)).trans
        (pairShuffle X.basis Y.basis (X.tensorPower n).basis (Y.tensorPower n).basis)

def repeatedPortsIndex (X Y : FiniteSystem) (n : ℕ) :
    TensorIndex (X.prod Y).basis n ≃ ((X.tensorPower n).prod (Y.tensorPower n)).basis :=
  (frontTailIndex (X.prod Y) n).symm.trans (matrixPowerPairIndex X Y n)

def groupedProductChannel {I O X Y I' O' X' Y' : FiniteSystem}
    (Φ : FiniteCPTP (I.prod X).basis (O.prod Y).basis)
    (Ψ : FiniteCPTP (I'.prod X').basis (O'.prod Y').basis) :
    FiniteCPTP ((I.prod I').prod (X.prod X')).basis
      ((O.prod O').prod (Y.prod Y')).basis :=
  composeChannel (reindexChannel (pairShuffle O.basis Y.basis O'.basis Y'.basis))
    (composeChannel (productChannel Φ Ψ)
      (reindexChannel (pairShuffle I.basis X.basis I'.basis X'.basis).symm))

def threePairIndex (R I X R' I' X' : Type*) :
    ((R × (I × X)) × (R' × (I' × X'))) ≃
      ((R × R') × ((I × I') × (X × X'))) where
  toFun a := ((a.1.1, a.2.1), ((a.1.2.1, a.2.2.1), (a.1.2.2, a.2.2.2)))
  invFun a := ((a.1.1, (a.2.1.1, a.2.2.1)), (a.1.2, (a.2.1.2, a.2.2.2)))
  left_inv _ := rfl
  right_inv _ := rfl

theorem extend_product_pre {I O C D R I' O' C' D' R' X Y X' Y' : FiniteSystem}
    (Θ : FiniteSuperchannel I.basis O.basis C.basis D.basis R.basis)
    (Ψ : FiniteSuperchannel I'.basis O'.basis C'.basis D'.basis R'.basis)
    (A : Matrix ((C.prod X).prod (C'.prod X')).basis
      ((C.prod X).prod (C'.prod X')).basis ℂ) :
    (extendSidePorts (productSuperchannel Θ Ψ) (X.prod X') (Y.prod Y')).pre.map
        (reindexMap (pairShuffle C.basis X.basis C'.basis X'.basis) A) =
      reindexMap (threePairIndex R.basis I.basis X.basis R'.basis I'.basis X'.basis)
        (productLinear (extendSidePorts Θ X Y).pre.map
          (extendSidePorts Ψ X' Y').pre.map A) := by
  ext ⟨⟨r, r'⟩, ⟨⟨i, i'⟩, ⟨x, x'⟩⟩⟩ ⟨⟨s, s'⟩, ⟨⟨j, j'⟩, ⟨z, z'⟩⟩⟩
  rfl

theorem extend_product_post {I O C D R I' O' C' D' R' X Y X' Y' : FiniteSystem}
    (Θ : FiniteSuperchannel I.basis O.basis C.basis D.basis R.basis)
    (Ψ : FiniteSuperchannel I'.basis O'.basis C'.basis D'.basis R'.basis)
    (A : Matrix ((R.prod (O.prod Y)).prod (R'.prod (O'.prod Y'))).basis
      ((R.prod (O.prod Y)).prod (R'.prod (O'.prod Y'))).basis ℂ) :
    (extendSidePorts (productSuperchannel Θ Ψ) (X.prod X') (Y.prod Y')).post.map
        (reindexMap (threePairIndex R.basis O.basis Y.basis R'.basis O'.basis Y'.basis) A) =
      reindexMap (pairShuffle D.basis Y.basis D'.basis Y'.basis)
        (productLinear (extendSidePorts Θ X Y).post.map
          (extendSidePorts Ψ X' Y').post.map A) := by
  ext ⟨⟨d, d'⟩, ⟨y, y'⟩⟩ ⟨⟨e, e'⟩, ⟨z, z'⟩⟩
  rfl

theorem grouped_reference_apply {I O R X Y I' O' R' X' Y' : FiniteSystem}
    (Φ : FiniteCPTP (I.prod X).basis (O.prod Y).basis)
    (Ψ : FiniteCPTP (I'.prod X').basis (O'.prod Y').basis)
    (A : Matrix ((R.prod (I.prod X)).prod (R'.prod (I'.prod X'))).basis
      ((R.prod (I.prod X)).prod (R'.prod (I'.prod X'))).basis ℂ) :
    amplifyLeftMap (groupedProductChannel Φ Ψ).map (R.basis × R'.basis)
        (reindexMap (threePairIndex R.basis I.basis X.basis R'.basis I'.basis X'.basis) A) =
      reindexMap (threePairIndex R.basis O.basis Y.basis R'.basis O'.basis Y'.basis)
        (productLinear (amplifyLeftMap Φ.map R.basis) (amplifyLeftMap Ψ.map R'.basis) A) := by
  ext ⟨⟨r, r'⟩, ⟨⟨o, o'⟩, ⟨y, y'⟩⟩⟩ ⟨⟨s, s'⟩, ⟨⟨p, p'⟩, ⟨z, z'⟩⟩⟩
  rfl

theorem groupedSideProduct_apply {I O C D R I' O' C' D' R' X Y X' Y' : FiniteSystem}
    (Θ : FiniteSuperchannel I.basis O.basis C.basis D.basis R.basis)
    (Ψ : FiniteSuperchannel I'.basis O'.basis C'.basis D'.basis R'.basis)
    (Φ : FiniteCPTP (I.prod X).basis (O.prod Y).basis)
    (Φ' : FiniteCPTP (I'.prod X').basis (O'.prod Y').basis)
    (A : Matrix ((C.prod X).prod (C'.prod X')).basis
      ((C.prod X).prod (C'.prod X')).basis ℂ) :
    ((extendSidePorts (productSuperchannel Θ Ψ) (X.prod X') (Y.prod Y')).applyChannel
        (groupedProductChannel Φ Φ')).map
      (reindexMap (pairShuffle C.basis X.basis C'.basis X'.basis) A) =
      reindexMap (pairShuffle D.basis Y.basis D'.basis Y'.basis)
        ((productChannel ((extendSidePorts Θ X Y).applyChannel Φ)
          ((extendSidePorts Ψ X' Y').applyChannel Φ')).map A) := by
  change (extendSidePorts (productSuperchannel Θ Ψ) (X.prod X') (Y.prod Y')).post.map
    (amplifyLeftMap (groupedProductChannel Φ Φ').map (R.basis × R'.basis)
      ((extendSidePorts (productSuperchannel Θ Ψ) (X.prod X') (Y.prod Y')).pre.map
        (reindexMap (pairShuffle C.basis X.basis C'.basis X'.basis) A))) = _
  rw [extend_product_pre, grouped_reference_apply, extend_product_post]
  change reindexMap (pairShuffle D.basis Y.basis D'.basis Y'.basis)
    (productLinear (extendSidePorts Θ X Y).post.map (extendSidePorts Ψ X' Y').post.map
      (productLinear (amplifyLeftMap Φ.map R.basis) (amplifyLeftMap Φ'.map R'.basis)
        (productLinear (extendSidePorts Θ X Y).pre.map (extendSidePorts Ψ X' Y').pre.map A))) =
      reindexMap (pairShuffle D.basis Y.basis D'.basis Y'.basis)
        (productLinear ((extendSidePorts Θ X Y).applyLinear Φ.map)
          ((extendSidePorts Ψ X' Y').applyLinear Φ'.map) A)
  rw [FiniteSuperchannel.applyLinear, FiniteSuperchannel.applyLinear,
    productLinear_comp_matrix, productLinear_comp_matrix]
  rfl

theorem reindexMap_trans_matrix {A B C : Type*}
    [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (e : A ≃ B) (f : B ≃ C) (M : Matrix A A ℂ) :
    reindexMap f (reindexMap e M) = reindexMap (e.trans f) M := rfl

theorem reindexMap_product_matrix {A B C D : Type*}
    [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D]
    (e : A ≃ C) (f : B ≃ D) (M : Matrix A A ℂ) (N : Matrix B B ℂ) :
    reindexMap (Equiv.prodCongr e f) (M ⊗ₖ N) =
      reindexMap e M ⊗ₖ reindexMap f N := rfl

theorem reindexMap_cancel_matrix {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (e : A ≃ B) (M : Matrix A A ℂ) :
    reindexMap e.symm (reindexMap e M) = M := by
  ext i j
  simp [reindexMap, Matrix.reindex_apply, Matrix.submatrix_apply]

def groupedSidePower {I O X Y : FiniteSystem}
    (Φ : FiniteCPTP (I.prod X).basis (O.prod Y).basis) :
    (n : ℕ) → FiniteCPTP ((I.tensorPower n).prod (X.tensorPower n)).basis
      ((O.tensorPower n).prod (Y.tensorPower n)).basis
  | 0 => reindexChannel (Equiv.refl (Unit × Unit))
  | n + 1 => groupedProductChannel Φ (groupedSidePower Φ n)

theorem groupedSidePower_intertwine {I O C D R X Y : FiniteSystem}
    (Θ : FiniteSuperchannel I.basis O.basis C.basis D.basis R.basis)
    (Φ : FiniteCPTP (I.prod X).basis (O.prod Y).basis) (n : ℕ)
    (A : Matrix ((C.prod X).tensorPower n).basis ((C.prod X).tensorPower n).basis ℂ) :
    (parallelChannel Θ n (X.tensorPower n) (Y.tensorPower n) (groupedSidePower Φ n)).map
        (reindexMap (matrixPowerPairIndex C X n) A) =
      reindexMap (matrixPowerPairIndex D Y n)
        ((matrixChannelPower ((extendSidePorts Θ X Y).applyChannel Φ) n).map A) := by
  induction n with
  | zero =>
      ext ⟨d, y⟩ ⟨e, z⟩
      cases d
      cases y
      cases e
      cases z
      rfl
  | succ n ih =>
      have hm :
          (parallelChannel Θ (n + 1) (X.tensorPower (n + 1)) (Y.tensorPower (n + 1))
            (groupedSidePower Φ (n + 1))).map.comp
              (reindexMap (matrixPowerPairIndex C X (n + 1))) =
          (reindexMap (matrixPowerPairIndex D Y (n + 1))).comp
            (matrixChannelPower ((extendSidePorts Θ X Y).applyChannel Φ) (n + 1)).map := by
        apply matrixMap_ext_units
        intro ⟨i, is⟩ ⟨j, js⟩
        have hs : Matrix.single (i, is) (j, js) (1 : ℂ) =
            Matrix.single i j 1 ⊗ₖ Matrix.single is js 1 := by
          rw [Matrix.single_kronecker_single, one_mul]
        simp only [LinearMap.comp_apply]
        rw [hs]
        change
          ((extendSidePorts (productSuperchannel Θ (parallelPower Θ n))
            (X.prod (X.tensorPower n)) (Y.prod (Y.tensorPower n))).applyChannel
              (groupedProductChannel Φ (groupedSidePower Φ n))).map
            (reindexMap (pairShuffle C.basis X.basis (C.tensorPower n).basis
              (X.tensorPower n).basis)
                (Matrix.single i j 1 ⊗ₖ
                  reindexMap (matrixPowerPairIndex C X n) (Matrix.single is js 1))) = _
        rw [groupedSideProduct_apply, productChannel_kronecker]
        change reindexMap (pairShuffle D.basis Y.basis (D.tensorPower n).basis
          (Y.tensorPower n).basis)
          (((extendSidePorts Θ X Y).applyChannel Φ).map (Matrix.single i j 1) ⊗ₖ
            (parallelChannel Θ n (X.tensorPower n) (Y.tensorPower n)
              (groupedSidePower Φ n)).map
                (reindexMap (matrixPowerPairIndex C X n) (Matrix.single is js 1))) = _
        rw [ih]
        change reindexMap (pairShuffle D.basis Y.basis (D.tensorPower n).basis
          (Y.tensorPower n).basis)
          (((extendSidePorts Θ X Y).applyChannel Φ).map (Matrix.single i j 1) ⊗ₖ
            reindexMap (matrixPowerPairIndex D Y n)
              ((matrixChannelPower ((extendSidePorts Θ X Y).applyChannel Φ) n).map
                (Matrix.single is js 1))) = _
        have hp :
            (matrixChannelPower ((extendSidePorts Θ X Y).applyChannel Φ) (n + 1)).map
                (Matrix.single i j 1 ⊗ₖ Matrix.single is js 1) =
              ((extendSidePorts Θ X Y).applyChannel Φ).map (Matrix.single i j 1) ⊗ₖ
                (matrixChannelPower ((extendSidePorts Θ X Y).applyChannel Φ) n).map
                  (Matrix.single is js 1) := productChannel_kronecker _ _ _ _
        rw [hp]
        rfl
      exact congrArg (fun F => F A) hm

theorem groupedSidePower_tensor_output {I O C D R X Y : FiniteSystem}
    (Θ : FiniteSuperchannel I.basis O.basis C.basis D.basis R.basis)
    (Φ : FiniteCPTP (I.prod X).basis (O.prod Y).basis)
    (A : Matrix (C.prod X).basis (C.prod X).basis ℂ) (n : ℕ) :
    (parallelChannel Θ n (X.tensorPower n) (Y.tensorPower n) (groupedSidePower Φ n)).map
        (reindexMap (repeatedPortsIndex C X n) (tensorPower A n)) =
      reindexMap (repeatedPortsIndex D Y n)
        (tensorPower (((extendSidePorts Θ X Y).applyChannel Φ).map A) n) := by
  change (parallelChannel Θ n (X.tensorPower n) (Y.tensorPower n) (groupedSidePower Φ n)).map
    (reindexMap (matrixPowerPairIndex C X n)
      (reindexMap (frontTailIndex (C.prod X) n).symm (tensorPower A n))) =
    reindexMap (matrixPowerPairIndex D Y n)
      (reindexMap (frontTailIndex (D.prod Y) n).symm
        (tensorPower (((extendSidePorts Θ X Y).applyChannel Φ).map A) n))
  rw [← matrixTensorPower_transport A n, reindexMap_cancel_matrix,
    groupedSidePower_intertwine, matrixChannelPower_tensor_output,
    ← matrixTensorPower_transport (((extendSidePorts Θ X Y).applyChannel Φ).map A) n,
    reindexMap_cancel_matrix]

theorem reindex_isDensity_matrix {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (e : A ≃ B)
    {ρ : Matrix A A ℂ} (hρ : IsDensity ρ) : IsDensity (reindexMap e ρ) :=
  channel_density (reindexChannel e) hρ.1 hρ.2

theorem reindex_isEffect_matrix {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (e : A ≃ B)
    {E : Matrix A A ℂ} (hE : IsEffect E) : IsEffect (reindexMap e E) := by
  refine ⟨hE.1.submatrix e.symm, ?_⟩
  have hc := hE.2.submatrix e.symm
  change ((1 : Matrix A A ℂ).submatrix e.symm e.symm -
    E.submatrix e.symm e.symm).PosSemidef at hc
  rw [Matrix.submatrix_one_equiv] at hc
  exact hc

theorem acceptanceProbability_reindex_matrix {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (e : A ≃ B) (ρ E : Matrix A A ℂ) :
    acceptanceProbability (reindexMap e ρ) (reindexMap e E) =
      acceptanceProbability ρ E := by
  unfold acceptanceProbability
  have hm : reindexMap e ρ * reindexMap e E = reindexMap e (ρ * E) :=
    ((Matrix.reindexRingEquiv ℂ e).map_mul ρ E).symm
  rw [hm]
  exact congrArg Complex.re (reindexMap_tracePreserving e (ρ * E))

def repeatedParallelTest {I O C D R₁ R₂ X Y : FiniteSystem}
    (Θ₁ : FiniteSuperchannel I.basis O.basis C.basis D.basis R₁.basis)
    (Θ₂ : FiniteSuperchannel I.basis O.basis C.basis D.basis R₂.basis)
    (Φ : FiniteCPTP (I.prod X).basis (O.prod Y).basis)
    (ρ : Matrix (C.prod X).basis (C.prod X).basis ℂ) (hρ : IsDensity ρ)
    (n : ℕ) (E : Matrix (TensorIndex (D.prod Y).basis n) (TensorIndex (D.prod Y).basis n) ℂ)
    (hE : IsEffect E) : BinaryTest :=
  parallelBinaryTest Θ₁ Θ₂ n (X.tensorPower n) (Y.tensorPower n) (groupedSidePower Φ n)
    (reindexMap (repeatedPortsIndex C X n) (tensorPower ρ n))
    (reindexMap (repeatedPortsIndex D Y n) E)
    (reindex_isDensity_matrix _ (tensorPower_isDensity hρ n))
    (reindex_isEffect_matrix _ hE)

theorem repeatedParallelTest_eq_iid {I O C D R₁ R₂ X Y : FiniteSystem}
    (Θ₁ : FiniteSuperchannel I.basis O.basis C.basis D.basis R₁.basis)
    (Θ₂ : FiniteSuperchannel I.basis O.basis C.basis D.basis R₂.basis)
    (Φ : FiniteCPTP (I.prod X).basis (O.prod Y).basis)
    (ρ : Matrix (C.prod X).basis (C.prod X).basis ℂ) (hρ : IsDensity ρ)
    (n : ℕ) (E : Matrix (TensorIndex (D.prod Y).basis n) (TensorIndex (D.prod Y).basis n) ℂ)
    (hE : IsEffect E) :
    repeatedParallelTest Θ₁ Θ₂ Φ ρ hρ n E hE =
      QuantumSteinAchievability.binaryTestOfEffect
        (tensorPower (((extendSidePorts Θ₁ X Y).applyChannel Φ).map ρ) n)
        (tensorPower (((extendSidePorts Θ₂ X Y).applyChannel Φ).map ρ) n)
        (tensorPower_isDensity (channel_density _ hρ.1 hρ.2) n)
        (tensorPower_isDensity (channel_density _ hρ.1 hρ.2) n) E hE := by
  apply Corollaries.binaryTest_ext
  · change 1 - acceptanceProbability
        ((parallelChannel Θ₁ n (X.tensorPower n) (Y.tensorPower n) (groupedSidePower Φ n)).map
          (reindexMap (repeatedPortsIndex C X n) (tensorPower ρ n)))
        (reindexMap (repeatedPortsIndex D Y n) E) =
      acceptanceProbability (tensorPower (((extendSidePorts Θ₁ X Y).applyChannel Φ).map ρ) n)
        (1 - E)
    rw [groupedSidePower_tensor_output, acceptanceProbability_reindex_matrix,
      QuantumSteinAchievability.acceptanceProbability_complement
        (tensorPower_isDensity (channel_density _ hρ.1 hρ.2) n)]
  · change acceptanceProbability
        ((parallelChannel Θ₂ n (X.tensorPower n) (Y.tensorPower n) (groupedSidePower Φ n)).map
          (reindexMap (repeatedPortsIndex C X n) (tensorPower ρ n)))
        (reindexMap (repeatedPortsIndex D Y n) E) =
      acceptanceProbability (tensorPower (((extendSidePorts Θ₂ X Y).applyChannel Φ).map ρ) n) E
    rw [groupedSidePower_tensor_output, acceptanceProbability_reindex_matrix]

def steinTailIndex (A : Type*) : (n : ℕ) →
    TensorPinching.RecursiveRows A n ≃ TensorIndex A n
  | 0 => Equiv.refl PUnit
  | n + 1 => Equiv.prodCongr (steinTailIndex A n) (Equiv.refl A)

theorem steinTensorPower_transport {A : Type*} [Fintype A] [DecidableEq A]
    (ρ : Matrix A A ℂ) (n : ℕ) :
    reindexMap (steinTailIndex A n) (TensorPinching.recursiveTensorPower ρ n) =
      tensorPower ρ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change reindexMap (Equiv.prodCongr (steinTailIndex A n) (Equiv.refl A))
        (TensorPinching.recursiveTensorPower ρ n ⊗ₖ ρ) = tensorPower ρ n ⊗ₖ ρ
      rw [reindexMap_product_matrix, ih]
      rfl

theorem steinBinaryTest_tail_transport {A : Type*} [Fintype A] [DecidableEq A]
    (ρ σ : Matrix A A ℂ) (hρ : IsDensity ρ) (hσ : IsDensity σ)
    (n : ℕ) (E : Matrix (TensorPinching.RecursiveRows A n)
      (TensorPinching.RecursiveRows A n) ℂ) (hE : IsEffect E) :
    QuantumSteinAchievability.binaryTestOfEffect
        (TensorPinching.recursiveTensorPower ρ n) (TensorPinching.recursiveTensorPower σ n)
        (PetzTensorTail.recursiveTensorPower_density hρ n)
        (PetzTensorTail.recursiveTensorPower_density hσ n) E hE =
      QuantumSteinAchievability.binaryTestOfEffect (tensorPower ρ n) (tensorPower σ n)
        (tensorPower_isDensity hρ n) (tensorPower_isDensity hσ n)
        (reindexMap (steinTailIndex A n) E) (reindex_isEffect_matrix _ hE) := by
  apply Corollaries.binaryTest_ext
  · rw [QuantumSteinAchievability.binaryTestOfEffect_alpha,
      QuantumSteinAchievability.binaryTestOfEffect_alpha,
      QuantumSteinAchievability.acceptanceProbability_complement
        (PetzTensorTail.recursiveTensorPower_density hρ n),
      QuantumSteinAchievability.acceptanceProbability_complement (tensorPower_isDensity hρ n),
      ← steinTensorPower_transport ρ n, acceptanceProbability_reindex_matrix]
  · rw [QuantumSteinAchievability.binaryTestOfEffect_beta,
      QuantumSteinAchievability.binaryTestOfEffect_beta,
      ← steinTensorPower_transport σ n, acceptanceProbability_reindex_matrix]

theorem iidStrategyFamily_embed_parallel {I O C D R₁ R₂ X Y : FiniteSystem}
    (Θ₁ : FiniteSuperchannel I.basis O.basis C.basis D.basis R₁.basis)
    (Θ₂ : FiniteSuperchannel I.basis O.basis C.basis D.basis R₂.basis)
    (Φ : FiniteCPTP (I.prod X).basis (O.prod Y).basis)
    (ρ : Matrix (C.prod X).basis (C.prod X).basis ℂ) (hρ : IsDensity ρ) :
    ∀ n, QuantumSteinAchievability.iidStrategyFamily
        (((extendSidePorts Θ₁ X Y).applyChannel Φ).map ρ)
        (((extendSidePorts Θ₂ X Y).applyChannel Φ).map ρ)
        (channel_density _ hρ.1 hρ.2) (channel_density _ hρ.1 hρ.2) n ⊆
      parallelStrategyFamily Θ₁ Θ₂ n := by
  intro n T hT
  rcases hT with ⟨⟨E, hE⟩, rfl⟩
  change QuantumSteinAchievability.binaryTestOfEffect
    (TensorPinching.recursiveTensorPower (((extendSidePorts Θ₁ X Y).applyChannel Φ).map ρ) n)
    (TensorPinching.recursiveTensorPower (((extendSidePorts Θ₂ X Y).applyChannel Φ).map ρ) n)
    (PetzTensorTail.recursiveTensorPower_density (channel_density _ hρ.1 hρ.2) n)
    (PetzTensorTail.recursiveTensorPower_density (channel_density _ hρ.1 hρ.2) n) E hE ∈
      parallelStrategyFamily Θ₁ Θ₂ n
  rw [steinBinaryTest_tail_transport
    (((extendSidePorts Θ₁ X Y).applyChannel Φ).map ρ)
    (((extendSidePorts Θ₂ X Y).applyChannel Φ).map ρ)
    (channel_density _ hρ.1 hρ.2) (channel_density _ hρ.1 hρ.2) n E hE,
    ← repeatedParallelTest_eq_iid Θ₁ Θ₂ Φ ρ hρ n
      (reindexMap (steinTailIndex (D.prod Y).basis n) E) (reindex_isEffect_matrix _ hE)]
  exact parallel_binaryTest_mem _ _ _ _ _ _ _ _ _ _

theorem output_relativeEntropyBits_le_parallel_exponent {I O C D R₁ R₂ X Y : FiniteSystem}
    (Θ₁ : FiniteSuperchannel I.basis O.basis C.basis D.basis R₁.basis)
    (Θ₂ : FiniteSuperchannel I.basis O.basis C.basis D.basis R₂.basis)
    (Φ : FiniteCPTP (I.prod X).basis (O.prod Y).basis)
    (ρ : Matrix (C.prod X).basis (C.prod X).basis ℂ) (hρ : IsDensity ρ) :
    relativeEntropyBits (((extendSidePorts Θ₁ X Y).applyChannel Φ).map ρ)
        (((extendSidePorts Θ₂ X Y).applyChannel Φ).map ρ) ≤
      orderedSteinExponent (parallelStrategyFamily Θ₁ Θ₂) :=
  (Corollaries.relativeEntropyBits_le_iid_orderedSteinExponent _ _
    (channel_density _ hρ.1 hρ.2) (channel_density _ hρ.1 hρ.2)).trans
      (orderedSteinExponent_mono_family (iidStrategyFamily_embed_parallel Θ₁ Θ₂ Φ ρ hρ))

end QuantumProver.SuperchannelDiscrimination.MatrixParallelPowerJoins
