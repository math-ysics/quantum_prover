import QuantumProver.InformationTheory.ElegantJointMeasurement.NuclearChoi
import QuantumProver.QuantumChannels.NuclearTensor

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open scoped InnerProductSpace ComplexOrder

namespace QuantumProver.ElegantJointMeasurement.NuclearProjectionSupport

open QuantumProver.NuclearOperator QuantumProver.HilbertNuclearCompression

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance nuclearNormedGroup : NormedAddCommGroup (Nuclear ℂ H H) := inferInstance
local instance nuclearNormedSpace : NormedSpace ℂ (Nuclear ℂ H H) := inferInstance

def complement (P : H →L[ℂ] H) : H →L[ℂ] H := ContinuousLinearMap.id ℂ H-P

theorem complement_adjoint (P : H →L[ℂ] H) (hAdj : P.adjoint=P) :
    (complement P).adjoint=complement P := by
  simp [complement,hAdj]

theorem complement_idempotent (P : H →L[ℂ] H) (hId : P.comp P=P) :
    (complement P).comp (complement P)=complement P := by
  ext x
  have hx : P (P x)=P x := congrArg (fun L : H →L[ℂ] H => L x) hId
  simp only [complement,ContinuousLinearMap.comp_apply,sub_apply,
    ContinuousLinearMap.id_apply,map_sub,hx]
  abel

theorem trace_compose_cycle (U : Nuclear ℂ H H) (L R : H →L[ℂ] H) :
    QuantumProver.HilbertNuclearTrace.trace (compose L R U)=
      QuantumProver.HilbertNuclearTrace.trace
        (compose (R.comp L) (ContinuousLinearMap.id ℂ H) U) := by
  have h : (QuantumProver.HilbertNuclearTrace.trace (𝕜 := ℂ) (E := H)) ∘L compose L R=
      (QuantumProver.HilbertNuclearTrace.trace (𝕜 := ℂ) (E := H)) ∘L
        compose (R.comp L) (ContinuousLinearMap.id ℂ H) := by
    apply QuantumProver.MatrixNuclearTensor.nuclear_clm_ext_rankOne
    intro phi y
    simp only [ContinuousLinearMap.comp_apply,compose_rankOne,
      QuantumProver.HilbertNuclearTrace.trace_rankOne,ContinuousLinearMap.id_apply]
  exact congrArg (fun f : Nuclear ℂ H H →L[ℂ] ℂ => f U) h

theorem trace_sandwich_idempotent (U : Nuclear ℂ H H) (P : H →L[ℂ] H)
    (hId : P.comp P=P) :
    QuantumProver.HilbertNuclearTrace.trace (compose P P U)=
      QuantumProver.HilbertNuclearTrace.trace (compose P (ContinuousLinearMap.id ℂ H) U) := by
  rw [trace_compose_cycle,hId]

theorem complement_trace_complex_identity (U : Nuclear ℂ H H) (P : H →L[ℂ] H)
    (hId : P.comp P=P) :
    QuantumProver.HilbertNuclearTrace.trace (compose (complement P) (complement P) U)=
      QuantumProver.HilbertNuclearTrace.trace U-QuantumProver.HilbertNuclearTrace.trace (compose P P U) := by
  have hlin : compose (complement P) (ContinuousLinearMap.id ℂ H) U=
      U-compose P (ContinuousLinearMap.id ℂ H) U := by
    apply toOperator_injective
    ext x
    simp only [toOperator_compose,map_sub,sub_apply,ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply,complement]
  rw [trace_sandwich_idempotent U (complement P) (complement_idempotent P hId),
    hlin,map_sub,← trace_sandwich_idempotent U P hId]

theorem complement_trace_identity (U : Nuclear ℂ H H) (P : H →L[ℂ] H)
    (hId : P.comp P=P) :
    (QuantumProver.HilbertNuclearTrace.trace (compose (complement P) (complement P) U)).re=
      (QuantumProver.HilbertNuclearTrace.trace U).re-
        (QuantumProver.HilbertNuclearTrace.trace (compose P P U)).re := by
  rw [complement_trace_complex_identity U P hId,Complex.sub_re]

theorem nuclear_sandwich_isPositive (U : Nuclear ℂ H H) (P : H →L[ℂ] H)
    (hU : (toOperator U).IsPositive) (hAdj : P.adjoint=P) :
    (toOperator (compose P P U)).IsPositive := by
  rw [toOperator_compose]
  simpa only [hAdj] using hU.conj_adjoint P

theorem positive_nuclear_re_trace_nonneg (U : Nuclear ℂ H H)
    (hU : (toOperator U).IsPositive) : 0 ≤ (QuantumProver.HilbertNuclearTrace.trace U).re := by
  obtain ⟨w,b,hb⟩ := exists_hilbertBasis ℂ H
  rw [← QuantumProver.ElegantJointMeasurement.NuclearChoi.norm_positive_nuclear_eq_re_trace b U hU]
  exact norm_nonneg U

theorem positive_nuclear_eq_zero_of_re_trace_eq_zero (U : Nuclear ℂ H H)
    (hU : (toOperator U).IsPositive) (hTrace : (QuantumProver.HilbertNuclearTrace.trace U).re=0) :
    U=0 := by
  apply norm_eq_zero.mp
  obtain ⟨w,b,hb⟩ := exists_hilbertBasis ℂ H
  rw [QuantumProver.ElegantJointMeasurement.NuclearChoi.norm_positive_nuclear_eq_re_trace b U hU,hTrace]

theorem projection_complement_sandwich_eq_zero (U : Nuclear ℂ H H)
    (P : H →L[ℂ] H) (hU : (toOperator U).IsPositive) (hAdj : P.adjoint=P)
    (hTrace : (QuantumProver.HilbertNuclearTrace.trace
      (compose (complement P) (complement P) U)).re=0) :
    compose (complement P) (complement P) U=0 :=
  positive_nuclear_eq_zero_of_re_trace_eq_zero _
    (nuclear_sandwich_isPositive U (complement P) hU (complement_adjoint P hAdj)) hTrace

theorem sqrt_annihilates_of_sandwich_eq_zero (D Q : H →L[ℂ] H)
    (hD : D.IsPositive) (hQ : Q.adjoint=Q) (hZero : Q ∘L D ∘L Q=0) :
    CFC.sqrt D ∘L Q=0 ∧ Q ∘L CFC.sqrt D=0 := by
  have hSAdj : (CFC.sqrt D).adjoint=CFC.sqrt D := QuantumProver.ElegantJointMeasurement.HilbertChoi.sqrt_adjoint_eq D
  have hSS : CFC.sqrt D ∘L CFC.sqrt D=D := QuantumProver.ElegantJointMeasurement.HilbertChoi.sqrt_comp_sqrt D hD
  have hGram : (CFC.sqrt D ∘L Q).adjoint ∘L (CFC.sqrt D ∘L Q)=0 := by
    calc
      (CFC.sqrt D ∘L Q).adjoint ∘L (CFC.sqrt D ∘L Q)=
          Q ∘L (CFC.sqrt D ∘L CFC.sqrt D) ∘L Q := by
            rw [ContinuousLinearMap.adjoint_comp,hQ,hSAdj]
            simp only [ContinuousLinearMap.comp_assoc]
      _=Q ∘L D ∘L Q := by rw [hSS]
      _=0 := hZero
  have hSQ : CFC.sqrt D ∘L Q=0 := ContinuousLinearMap.adjoint_comp_self_eq_zero_iff.mp hGram
  refine ⟨hSQ,?_⟩
  simpa only [ContinuousLinearMap.adjoint_comp,hQ,hSAdj,map_zero] using
    congrArg (fun L : H →L[ℂ] H => L.adjoint) hSQ

theorem projection_sqrt_annihilates_of_re_complement_trace_eq_zero
    (U : Nuclear ℂ H H) (P : H →L[ℂ] H)
    (hU : (toOperator U).IsPositive) (hAdj : P.adjoint=P)
    (hTrace : (QuantumProver.HilbertNuclearTrace.trace
      (compose (complement P) (complement P) U)).re=0) :
    CFC.sqrt (toOperator U) ∘L complement P=0 ∧
      complement P ∘L CFC.sqrt (toOperator U)=0 := by
  have h := congrArg (toOperator (𝕜 := ℂ) (E := H) (F := H))
    (projection_complement_sandwich_eq_zero U P hU hAdj hTrace)
  rw [toOperator_compose,map_zero] at h
  exact sqrt_annihilates_of_sandwich_eq_zero _ _ hU (complement_adjoint P hAdj) h

theorem projection_sqrt_eq_of_re_complement_trace_eq_zero
    (U : Nuclear ℂ H H) (P : H →L[ℂ] H)
    (hU : (toOperator U).IsPositive) (hAdj : P.adjoint=P)
    (hTrace : (QuantumProver.HilbertNuclearTrace.trace
      (compose (complement P) (complement P) U)).re=0) :
    P.comp (CFC.sqrt (toOperator U))=CFC.sqrt (toOperator U) := by
  have hQS := (projection_sqrt_annihilates_of_re_complement_trace_eq_zero U P hU hAdj hTrace).2
  ext x
  have hx := congrArg (fun L : H →L[ℂ] H => L x) hQS
  change CFC.sqrt (toOperator U) x-P (CFC.sqrt (toOperator U) x)=0 at hx
  exact (sub_eq_zero.mp hx).symm

theorem projection_operator_annihilates_of_re_complement_trace_eq_zero
    (U : Nuclear ℂ H H) (P : H →L[ℂ] H)
    (hU : (toOperator U).IsPositive) (hAdj : P.adjoint=P)
    (hTrace : (QuantumProver.HilbertNuclearTrace.trace
      (compose (complement P) (complement P) U)).re=0) :
    toOperator U ∘L complement P=0 ∧ complement P ∘L toOperator U=0 := by
  obtain ⟨hSQ,hQS⟩ := projection_sqrt_annihilates_of_re_complement_trace_eq_zero U P hU hAdj hTrace
  have hSS := QuantumProver.ElegantJointMeasurement.HilbertChoi.sqrt_comp_sqrt (toOperator U) hU
  constructor
  · rw [← hSS,ContinuousLinearMap.comp_assoc,hSQ,ContinuousLinearMap.comp_zero]
  · rw [← hSS,← ContinuousLinearMap.comp_assoc,hQS,ContinuousLinearMap.zero_comp]

theorem projection_sandwich_eq_of_re_complement_trace_eq_zero
    (U : Nuclear ℂ H H) (P : H →L[ℂ] H)
    (hU : (toOperator U).IsPositive) (hAdj : P.adjoint=P) (hId : P.comp P=P)
    (hTrace : (QuantumProver.HilbertNuclearTrace.trace
      (compose (complement P) (complement P) U)).re=0) : compose P P U=U := by
  obtain ⟨hDQ,hQD⟩ := projection_operator_annihilates_of_re_complement_trace_eq_zero U P hU hAdj hTrace
  have hLeft : P ∘L toOperator U=toOperator U := by
    ext x
    have hx := congrArg (fun L : H →L[ℂ] H => L x) hQD
    change toOperator U x-P (toOperator U x)=0 at hx
    exact (sub_eq_zero.mp hx).symm
  have hRight : toOperator U ∘L P=toOperator U := by
    ext x
    have hx := congrArg (fun L : H →L[ℂ] H => L x) hDQ
    change toOperator U (x-P x)=0 at hx
    rw [map_sub] at hx
    exact (sub_eq_zero.mp hx).symm
  apply toOperator_injective
  rw [toOperator_compose,hRight,hLeft]

theorem projection_sandwich_eq_of_re_trace_eq (U : Nuclear ℂ H H) (P : H →L[ℂ] H)
    (hU : (toOperator U).IsPositive) (hAdj : P.adjoint=P) (hId : P.comp P=P)
    (hTrace : (QuantumProver.HilbertNuclearTrace.trace U).re=
      (QuantumProver.HilbertNuclearTrace.trace (compose P P U)).re) : compose P P U=U := by
  apply projection_sandwich_eq_of_re_complement_trace_eq_zero U P hU hAdj hId
  rw [complement_trace_identity U P hId,hTrace,sub_self]

theorem projection_sandwich_eq_of_trace_eq (U : Nuclear ℂ H H) (P : H →L[ℂ] H)
    (hU : (toOperator U).IsPositive) (hAdj : P.adjoint=P) (hId : P.comp P=P)
    (hTrace : QuantumProver.HilbertNuclearTrace.trace U=
      QuantumProver.HilbertNuclearTrace.trace (compose P P U)) : compose P P U=U :=
  projection_sandwich_eq_of_re_trace_eq U P hU hAdj hId (congrArg Complex.re hTrace)

theorem projection_sqrt_eq_of_re_trace_eq (U : Nuclear ℂ H H) (P : H →L[ℂ] H)
    (hU : (toOperator U).IsPositive) (hAdj : P.adjoint=P) (hId : P.comp P=P)
    (hTrace : (QuantumProver.HilbertNuclearTrace.trace U).re=
      (QuantumProver.HilbertNuclearTrace.trace (compose P P U)).re) :
    P.comp (CFC.sqrt (toOperator U))=CFC.sqrt (toOperator U) := by
  apply projection_sqrt_eq_of_re_complement_trace_eq_zero U P hU hAdj
  rw [complement_trace_identity U P hId,hTrace,sub_self]

theorem sqrt_vector_mem_range (U : Nuclear ℂ H H) (P : H →L[ℂ] H)
    (hU : (toOperator U).IsPositive) (hAdj : P.adjoint=P) (hId : P.comp P=P)
    (hTrace : (QuantumProver.HilbertNuclearTrace.trace U).re=
      (QuantumProver.HilbertNuclearTrace.trace (compose P P U)).re) (x : H) :
    CFC.sqrt (toOperator U) x ∈ P.toLinearMap.range := by
  exact ⟨CFC.sqrt (toOperator U) x,
    congrArg (fun L : H →L[ℂ] H => L x) (projection_sqrt_eq_of_re_trace_eq U P hU hAdj hId hTrace)⟩

theorem sqrt_column_mem_range {L : Type*} (b : HilbertBasis L ℂ H)
    (U : Nuclear ℂ H H) (P : H →L[ℂ] H)
    (hU : (toOperator U).IsPositive) (hAdj : P.adjoint=P) (hId : P.comp P=P)
    (hTrace : (QuantumProver.HilbertNuclearTrace.trace U).re=
      (QuantumProver.HilbertNuclearTrace.trace (compose P P U)).re) (l : L) :
    QuantumProver.ElegantJointMeasurement.HilbertChoi.squareRootColumn b (toOperator U) l ∈ P.toLinearMap.range :=
  sqrt_vector_mem_range U P hU hAdj hId hTrace (b l)

end QuantumProver.ElegantJointMeasurement.NuclearProjectionSupport
