import QuantumProver.InformationTheory.ElegantJointMeasurement.NormalInstrumentAbsorption
import QuantumProver.InformationTheory.ElegantJointMeasurement.HilbertRecovery
import QuantumProver.InformationTheory.SuperchannelDiscrimination.CPTPKraus

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory InnerProductSpace
open scoped BigOperators InnerProduct ComplexOrder MatrixOrder Topology Matrix.Norms.L2Operator

namespace QuantumProver.ElegantJointMeasurement.NormalFiniteTerminal

open QuantumProver.ElegantJointMeasurement.HilbertPolar QuantumProver.ElegantJointMeasurement.HilbertRecovery QuantumProver.ElegantJointMeasurement.NuclearChoi QuantumProver.ElegantJointMeasurement.HilbertChoi
open QuantumProver.ElegantJointMeasurement.NormalCPInstruments QuantumProver.ElegantJointMeasurement.NormalInstrumentAbsorption
open QuantumProver.NuclearOperator (toOperator toOperator_injective)
open QuantumProver.HilbertNuclearCompression

variable {I C : Type} [Fintype I] [DecidableEq I] [Fintype C] [DecidableEq C]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

local instance sourceComplete (K : Type) [Fintype K] : CompleteSpace (Source K) :=
  PiLp.completeSpace 2 (fun _ : K => ℂ)

local instance finiteNuclearDimensional : FiniteDimensional ℂ (Nuclear (Source C)) :=
  FiniteDimensional.of_injective
    (toOperator (𝕜 := ℂ) (E := Source C) (F := Source C)).toLinearMap toOperator_injective

def matrixDecodeLinear : Nuclear (Source C) →ₗ[ℂ] Matrix C C ℂ where
  toFun A i j := inner ℂ (EuclideanSpace.basisFun C ℂ i)
    (toOperator A (EuclideanSpace.basisFun C ℂ j))
  map_add' A B := by
    ext i j
    simp only [map_add, add_apply, inner_add_right, Matrix.add_apply]
  map_smul' z A := by
    ext i j
    simp only [map_smul, smul_apply, inner_smul_right, Matrix.smul_apply,
      RingHom.id_apply, smul_eq_mul]

def matrixDecode : Nuclear (Source C) →L[ℂ] Matrix C C ℂ :=
  matrixDecodeLinear.toContinuousLinearMap

@[simp] theorem matrixDecode_apply (A : Nuclear (Source C)) (i j : C) :
    matrixDecode A i j = inner ℂ (EuclideanSpace.basisFun C ℂ i)
      (toOperator A (EuclideanSpace.basisFun C ℂ j)) := rfl

theorem matrixOperator_matrixDecode (A : Nuclear (Source C)) :
    QuantumProver.ElegantJointMeasurement.HilbertPolar.matrixOperator (matrixDecode A) = toOperator A := by
  classical
  ext x i
  change (∑ j, matrixDecode A i j * x j) = (toOperator A x) i
  simp only [matrixDecode_apply, EuclideanSpace.basisFun_inner]
  have hx : (∑ j : C, x j • EuclideanSpace.basisFun C ℂ j) = x := by
    simpa only [EuclideanSpace.basisFun_inner] using (EuclideanSpace.basisFun C ℂ).sum_repr' x
  conv_rhs => rw [← hx, map_sum]
  simp only [map_smul, WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, smul_eq_mul,
    mul_comm]

@[simp] theorem nuclearMatrix_matrixDecode (A : Nuclear (Source C)) :
    nuclearMatrix (matrixDecode A) = A := by
  apply toOperator_injective
  rw [toOperator_nuclearMatrix, matrixOperator_matrixDecode]

@[simp] theorem matrixDecode_nuclearMatrix (X : Matrix C C ℂ) :
    matrixDecode (nuclearMatrix X) = X := by
  apply (QuantumProver.ElegantJointMeasurement.HilbertPolar.matrixOperator (I := C)).injective
  change QuantumProver.ElegantJointMeasurement.HilbertPolar.matrixOperator (matrixDecode (nuclearMatrix X)) =
    QuantumProver.ElegantJointMeasurement.HilbertPolar.matrixOperator X
  rw [matrixOperator_matrixDecode, toOperator_nuclearMatrix]

theorem matrixDecode_trace (A : Nuclear (Source C)) :
    Matrix.trace (matrixDecode A) = QuantumProver.HilbertNuclearTrace.trace A := by
  rw [← trace_nuclearMatrix (matrixDecode A), nuclearMatrix_matrixDecode]

theorem matrixDecode_posSemidef (A : Nuclear (Source C))
    (hA : (toOperator A).IsPositive) : (matrixDecode A).PosSemidef := by
  have h : 0 ≤ QuantumProver.ElegantJointMeasurement.HilbertPolar.matrixOperator (matrixDecode A) := by
    rw [matrixOperator_matrixDecode]
    exact ContinuousLinearMap.nonneg_iff_isPositive.mpr hA
  exact Matrix.nonneg_iff_posSemidef.mp (by
    simpa using map_nonneg (QuantumProver.ElegantJointMeasurement.HilbertPolar.matrixOperator (I := C)).symm h)

theorem matrixOperator_decoded_choi (A : PhysicalOperation I (Source C)) :
    QuantumProver.ElegantJointMeasurement.HilbertPolar.matrixOperator
        (QuantumProver.SuperchannelDiscrimination.CPTPKraus.choi (matrixDecode.comp A).toLinearMap) =
      (sourceCurry (R := I) (I := C)).adjoint ∘L
        QuantumProver.ElegantJointMeasurement.HilbertChoi.choi (operationOperator A.toLinearMap) ∘L
          sourceCurry (R := I) (I := C) := by
  classical
  ext x q
  rcases q with ⟨i,c⟩
  change (∑ p : I × C, matrixDecode (A (matrixUnit i p.1)) c p.2 * x p) = _
  simp only [Fintype.sum_prod_type, ContinuousLinearMap.comp_apply,
    sourceCurry_adjoint_apply, QuantumProver.ElegantJointMeasurement.HilbertChoi.choi, blockOperator_apply,
    operationOperator_apply, ContinuousLinearMap.coe_coe, WithLp.ofLp_sum, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro j _
  rw [← matrixOperator_matrixDecode (A (matrixUnit i j))]
  rfl

theorem completelyPositive_matrixDecode_comp (A : PhysicalOperation I (Source C))
    (hA : QuantumProver.ElegantJointMeasurement.HilbertChoi.CompletelyPositive (operationOperator A.toLinearMap)) :
    QuantumProver.SuperchannelDiscrimination.CPTPKraus.CompletelyPositive
      (matrixDecode.comp A).toLinearMap := by
  apply (QuantumProver.SuperchannelDiscrimination.CPTPKraus.choi_posSemidef_iff_completelyPositive _).mp
  have hn := QuantumProver.ElegantJointMeasurement.HilbertChoi.choi_isPositive (operationOperator A.toLinearMap) hA
  have hp := hn.conj_adjoint (sourceCurry (R := I) (I := C)).adjoint
  have h : 0 ≤ QuantumProver.ElegantJointMeasurement.HilbertPolar.matrixOperator
      (QuantumProver.SuperchannelDiscrimination.CPTPKraus.choi (matrixDecode.comp A).toLinearMap) := by
    rw [matrixOperator_decoded_choi]
    exact ContinuousLinearMap.nonneg_iff_isPositive.mpr
      (by simpa only [ContinuousLinearMap.adjoint_adjoint] using hp)
  exact Matrix.nonneg_iff_posSemidef.mp (by
    simpa using map_nonneg (QuantumProver.ElegantJointMeasurement.HilbertPolar.matrixOperator (I := I × C)).symm h)

def finiteTerminalMap (R : PhysicalOperation I E) (Psi : NormalOperation E (Source C)) :
    Matrix I I ℂ →L[ℂ] Matrix C C ℂ :=
  matrixDecode.comp (Psi.comp R)

@[simp] theorem finiteTerminalMap_apply (R : PhysicalOperation I E)
    (Psi : NormalOperation E (Source C)) (X : Matrix I I ℂ) :
    finiteTerminalMap R Psi X = matrixDecode (Psi (R X)) := rfl

theorem nuclearMatrix_finiteTerminalMap_apply (R : PhysicalOperation I E)
    (Psi : NormalOperation E (Source C)) (X : Matrix I I ℂ) :
    nuclearMatrix (finiteTerminalMap R Psi X) = Psi (R X) :=
  nuclearMatrix_matrixDecode (Psi (R X))

theorem completelyPositive_finiteTerminalMap (R : PhysicalOperation I E)
    (Psi : NormalOperation E (Source C))
    (hR : QuantumProver.ElegantJointMeasurement.HilbertChoi.CompletelyPositive (operationOperator R.toLinearMap))
    (hPsi : NormalCompletelyPositive Psi) :
    QuantumProver.SuperchannelDiscrimination.CPTPKraus.CompletelyPositive
      (finiteTerminalMap R Psi).toLinearMap :=
  completelyPositive_matrixDecode_comp (Psi.comp R) (completelyPositive_comp Psi hPsi R hR)

theorem trace_finiteTerminalMap (R : PhysicalOperation I E)
    (Psi : NormalOperation E (Source C))
    (hR : ∀ X, QuantumProver.HilbertNuclearTrace.trace (R X) = Matrix.trace X)
    (hPsi : ∀ T, QuantumProver.HilbertNuclearTrace.trace (Psi T) = QuantumProver.HilbertNuclearTrace.trace T)
    (X : Matrix I I ℂ) : Matrix.trace (finiteTerminalMap R Psi X) = Matrix.trace X := by
  rw [finiteTerminalMap_apply, matrixDecode_trace, hPsi, hR]

theorem tracePreserving_finiteTerminalMap (R : PhysicalOperation I E)
    (Psi : NormalOperation E (Source C))
    (hR : ∀ X, QuantumProver.HilbertNuclearTrace.trace (R X) = Matrix.trace X)
    (hPsi : ∀ T, QuantumProver.HilbertNuclearTrace.trace (Psi T) = QuantumProver.HilbertNuclearTrace.trace T) :
    QuantumProver.SuperchannelDiscrimination.CPTPKraus.TracePreserving
      (finiteTerminalMap R Psi).toLinearMap :=
  trace_finiteTerminalMap R Psi hR hPsi

def finiteMapFromUnits (A : I → I → Matrix C C ℂ) : Matrix I I ℂ →L[ℂ] Matrix C C ℂ :=
  ∑ i, ∑ j, (matrixEntry i j).smulRight (A i j)

theorem finiteMapFromUnits_apply (A : I → I → Matrix C C ℂ) (X : Matrix I I ℂ) :
    finiteMapFromUnits A X = ∑ i, ∑ j, X i j • A i j := by
  simp only [finiteMapFromUnits, sum_apply, ContinuousLinearMap.smulRight_apply, matrixEntry]
  rfl

theorem finiteMap_eq_fromUnits (Phi : Matrix I I ℂ →L[ℂ] Matrix C C ℂ) :
    Phi = finiteMapFromUnits (fun i j => Phi (matrixUnit i j)) := by
  apply ContinuousLinearMap.ext
  intro X
  rw [finiteMapFromUnits_apply]
  conv_lhs => rw [matrix_decomposition X]
  simp only [map_sum, map_smul]

local instance finiteChannelMeasurable : MeasurableSpace (Matrix I I ℂ →L[ℂ] Matrix C C ℂ) := borel _
local instance finiteChannelBorel : BorelSpace (Matrix I I ℂ →L[ℂ] Matrix C C ℂ) := ⟨rfl⟩

variable {H : Type*} [MeasurableSpace H]

theorem stronglyMeasurable_finiteMap_of_units
    (Phi : H → Matrix I I ℂ →L[ℂ] Matrix C C ℂ)
    (hPhi : ∀ i j, StronglyMeasurable (fun h => Phi h (matrixUnit i j))) :
    StronglyMeasurable Phi := by
  have he : Phi = fun h => finiteMapFromUnits (fun i j => Phi h (matrixUnit i j)) :=
    funext fun h => finiteMap_eq_fromUnits (Phi h)
  rw [he]
  unfold finiteMapFromUnits
  apply Finset.stronglyMeasurable_fun_sum
  intro i _
  apply Finset.stronglyMeasurable_fun_sum
  intro j _
  exact (ContinuousLinearMap.smulRightL ℂ (Matrix I I ℂ) (Matrix C C ℂ)
    (matrixEntry i j)).continuous.comp_stronglyMeasurable (hPhi i j)

theorem stronglyMeasurable_finiteTerminalMap_of_coordinates
    (R : H → PhysicalOperation I E) (Psi : H → NormalOperation E (Source C))
    (hcoord : ∀ i j c d, Measurable (fun h => inner ℂ (EuclideanSpace.basisFun C ℂ c)
      (toOperator (Psi h (R h (matrixUnit i j))) (EuclideanSpace.basisFun C ℂ d)))) :
    StronglyMeasurable (fun h => finiteTerminalMap (R h) (Psi h)) := by
  apply stronglyMeasurable_finiteMap_of_units
  intro i j
  have he : (fun h => finiteTerminalMap (R h) (Psi h) (matrixUnit i j)) =
      fun h => ∑ c, ∑ d, inner ℂ (EuclideanSpace.basisFun C ℂ c)
        (toOperator (Psi h (R h (matrixUnit i j))) (EuclideanSpace.basisFun C ℂ d)) • matrixUnit c d := by
    funext h
    exact matrix_decomposition (finiteTerminalMap (R h) (Psi h) (matrixUnit i j))
  rw [he]
  apply Finset.stronglyMeasurable_fun_sum
  intro c _
  apply Finset.stronglyMeasurable_fun_sum
  intro d _
  exact (hcoord i j c d).stronglyMeasurable.smul_const (matrixUnit c d)

theorem measurable_finiteTerminalMap
    (R : H → PhysicalOperation I E) (Psi : H → NormalOperation E (Source C))
    (hcoord : ∀ i j c d, Measurable (fun h => inner ℂ (EuclideanSpace.basisFun C ℂ c)
      (toOperator (Psi h (R h (matrixUnit i j))) (EuclideanSpace.basisFun C ℂ d)))) :
    Measurable (fun h => finiteTerminalMap (R h) (Psi h)) :=
  (stronglyMeasurable_finiteTerminalMap_of_coordinates R Psi hcoord).measurable

theorem stronglyMeasurable_finiteTerminalMap_of_coordinate_fields
    (R : H → PhysicalOperation I E) (Psi : H → NormalOperation E (Source C))
    (hR : ∀ X, StronglyMeasurable (fun h => R h X))
    (hPsi : ∀ T : Nuclear E, ∀ x y : Source C,
      Measurable (fun h => inner ℂ x (toOperator (Psi h T) y))) :
    StronglyMeasurable (fun h => finiteTerminalMap (R h) (Psi h)) := by
  have hfixed (T : Nuclear E) : StronglyMeasurable (fun h => Psi h T) :=
    stronglyMeasurable_of_weak_coordinates _ (hPsi T)
  apply stronglyMeasurable_finiteMap_of_units
  intro i j
  have ht := stronglyMeasurable_variable_apply Psi hfixed (fun h => R h (matrixUnit i j))
    (hR (matrixUnit i j))
  exact (matrixDecode (C := C)).continuous.comp_stronglyMeasurable ht

theorem measurable_finiteTerminalMap_of_coordinate_fields
    (R : H → PhysicalOperation I E) (Psi : H → NormalOperation E (Source C))
    (hR : ∀ X, StronglyMeasurable (fun h => R h X))
    (hPsi : ∀ T : Nuclear E, ∀ x y : Source C,
      Measurable (fun h => inner ℂ x (toOperator (Psi h T) y))) :
    Measurable (fun h => finiteTerminalMap (R h) (Psi h)) :=
  (stronglyMeasurable_finiteTerminalMap_of_coordinate_fields R Psi hR hPsi).measurable

theorem stronglyMeasurable_finiteTerminalMap_apply_of_coordinate_fields
    (R : H → PhysicalOperation I E) (Psi : H → NormalOperation E (Source C))
    (hR : ∀ X, StronglyMeasurable (fun h => R h X))
    (hPsi : ∀ T : Nuclear E, ∀ x y : Source C,
      Measurable (fun h => inner ℂ x (toOperator (Psi h T) y)))
    (X : H → Matrix I I ℂ) (hX : StronglyMeasurable X) :
    StronglyMeasurable (fun h => finiteTerminalMap (R h) (Psi h) (X h)) := by
  have hPhi := stronglyMeasurable_finiteTerminalMap_of_coordinate_fields R Psi hR hPsi
  have hc : Continuous (fun p : (Matrix I I ℂ →L[ℂ] Matrix C C ℂ) × Matrix I I ℂ => p.1 p.2) :=
    (isBoundedBilinearMap_apply (𝕜 := ℂ) (E := Matrix I I ℂ) (F := Matrix C C ℂ)).continuous
  exact hc.comp_stronglyMeasurable (hPhi.prodMk hX)

end QuantumProver.ElegantJointMeasurement.NormalFiniteTerminal
