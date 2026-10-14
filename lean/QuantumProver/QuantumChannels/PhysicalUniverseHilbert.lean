import QuantumProver.InformationTheory.ElegantJointMeasurement.NormalPhysicalAdmission

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory Set Function InnerProductSpace
open scoped BigOperators Topology Classical

namespace QuantumProver.MatrixPhysicalUniverseHilbert

open QuantumProver.ElegantJointMeasurement.NormalPhysicalAdmission QuantumProver.ElegantJointMeasurement.MeasurableHilbertField
open QuantumProver.ElegantJointMeasurement.MeasurableHilbertOperator QuantumProver.ElegantJointMeasurement.SeparableHilbertEmbedding

instance uliftInnerProductSpace.{r,v} (X : Type v) [NormedAddCommGroup X]
    [InnerProductSpace ℂ X] : InnerProductSpace ℂ (ULift.{r} X) where
  inner x y := inner ℂ x.down y.down
  add_left x y z := inner_add_left x.down y.down z.down
  smul_left x y c := inner_smul_left x.down y.down c
  norm_sq_eq_re_inner x := norm_sq_eq_re_inner x.down
  conj_inner_symm x y := inner_conj_symm x.down y.down

def uliftUnitary.{r,v} (X : Type v) [NormedAddCommGroup X]
    [InnerProductSpace ℂ X] : X ≃ₗᵢ[ℂ] ULift.{r} X :=
  (LinearIsometryEquiv.ulift ℂ X).symm

def uliftLinearIsometry.{r,s,v,w} {X : Type v} {Y : Type w}
    [NormedAddCommGroup X] [InnerProductSpace ℂ X]
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] (J : X →ₗᵢ[ℂ] Y) :
    ULift.{r} X →ₗᵢ[ℂ] ULift.{s} Y :=
  (uliftUnitary Y).toLinearIsometry.comp
    (J.comp (uliftUnitary X).symm.toLinearIsometry)

def uliftIsometryEquiv.{r,s,v,w} {X : Type v} {Y : Type w}
    [NormedAddCommGroup X] [InnerProductSpace ℂ X]
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] (J : X ≃ₗᵢ[ℂ] Y) :
    ULift.{r} X ≃ₗᵢ[ℂ] ULift.{s} Y :=
  (uliftUnitary X).symm.trans (J.trans (uliftUnitary Y))

def uliftOperator.{r,s,v,w} {X : Type v} {Y : Type w}
    [NormedAddCommGroup X] [InnerProductSpace ℂ X]
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] (T : X →L[ℂ] Y) :
    ULift.{r} X →L[ℂ] ULift.{s} Y :=
  (uliftUnitary Y).toLinearIsometry.toContinuousLinearMap.comp
    (T.comp (uliftUnitary X).symm.toLinearIsometry.toContinuousLinearMap)

def uliftFamily.{r,u,v} {Z : Type u} [MeasurableSpace Z] {E : Z → Type v}
    [∀ z, NormedAddCommGroup (E z)] [∀ z, InnerProductSpace ℂ (E z)]
    [∀ z, CompleteSpace (E z)] (F : FundamentalFamily E) :
    FundamentalFamily (fun z => ULift.{r} (E z)) :=
  transportFamily F (fun z => uliftUnitary (E z))

def uliftWiring.{r,s,u,v,w} (Ω : ℕ → Type u) [∀ n, MeasurableSpace (Ω n)]
    [∀ n, StandardBorelSpace (Ω n)] (D : PhysicalDomains Ω) (b : Bool)
    {E : (n : ℕ) → D.admissible n → Type v}
    [∀ n h, NormedAddCommGroup (E n h)] [∀ n h, InnerProductSpace ℂ (E n h)]
    [∀ n h, CompleteSpace (E n h)]
    (F : (n : ℕ) → FundamentalFamily (E n))
    {G : (n : ℕ) → D.actingDomain n b × Ω n → Type w}
    [∀ n z, NormedAddCommGroup (G n z)] [∀ n z, InnerProductSpace ℂ (G n z)]
    [∀ n z, CompleteSpace (G n z)]
    (Q : (n : ℕ) → FundamentalFamily (G n))
    (W : PhysicalMemoryWiring Ω D b F Q) :
    PhysicalMemoryWiring Ω D b (fun n => uliftFamily.{r} (F n))
      (fun n => uliftFamily.{s} (Q n)) where
  acted n h := uliftIsometryEquiv.{s,r} (W.acted n h)
  acted_measurable n i j := W.acted_measurable n i j
  idle n h := uliftIsometryEquiv.{r,r} (W.idle n h)
  idle_measurable n i j := W.idle_measurable n i j

universe r s u v w

section HilbertMaps

variable {X : Type v} {Y : Type w}
  [NormedAddCommGroup X] [InnerProductSpace ℂ X]
  [NormedAddCommGroup Y] [InnerProductSpace ℂ Y]

@[simp] theorem ulift_inner (x y : ULift.{r} X) :
    inner ℂ x y = inner ℂ x.down y.down := rfl

@[simp] theorem uliftUnitary_apply (x : X) :
    uliftUnitary.{r} X x = ULift.up x := rfl

@[simp] theorem uliftUnitary_symm_apply (x : ULift.{r} X) :
    (uliftUnitary X).symm x = x.down := rfl

@[simp] theorem uliftLinearIsometry_apply (J : X →ₗᵢ[ℂ] Y) (x : ULift.{r} X) :
    uliftLinearIsometry.{r,s} J x = ULift.up (J x.down) := rfl

@[simp] theorem uliftLinearIsometry_apply_up (J : X →ₗᵢ[ℂ] Y) (x : X) :
    uliftLinearIsometry.{r,s} J (ULift.up x) = ULift.up (J x) := rfl

@[simp] theorem uliftIsometryEquiv_apply (J : X ≃ₗᵢ[ℂ] Y) (x : ULift.{r} X) :
    uliftIsometryEquiv.{r,s} J x = ULift.up (J x.down) := rfl

@[simp] theorem uliftIsometryEquiv_apply_up (J : X ≃ₗᵢ[ℂ] Y) (x : X) :
    uliftIsometryEquiv.{r,s} J (ULift.up x) = ULift.up (J x) := rfl

@[simp] theorem uliftIsometryEquiv_symm_apply (J : X ≃ₗᵢ[ℂ] Y)
    (y : ULift.{s} Y) :
    (uliftIsometryEquiv.{r,s} J).symm y = ULift.up (J.symm y.down) := rfl

@[simp] theorem uliftOperator_apply (T : X →L[ℂ] Y) (x : ULift.{r} X) :
    uliftOperator.{r,s} T x = ULift.up (T x.down) := rfl

@[simp] theorem uliftOperator_apply_up (T : X →L[ℂ] Y) (x : X) :
    uliftOperator.{r,s} T (ULift.up x) = ULift.up (T x) := rfl

end HilbertMaps

section FundamentalFields

variable {Z : Type u} [MeasurableSpace Z] {E : Z → Type v}
  [∀ z, NormedAddCommGroup (E z)] [∀ z, InnerProductSpace ℂ (E z)]
  [∀ z, CompleteSpace (E z)]

@[simp] theorem uliftFamily_vector (F : FundamentalFamily E) (z : Z) (i : ℕ) :
    (uliftFamily.{r} F).vector z i = ULift.up (F.vector z i) := rfl

theorem uliftFamily_pairingMeasurable (F : FundamentalFamily E) (i j : ℕ) :
    Measurable (fun z => inner ℂ (ULift.up (F.vector z i) : ULift.{r} (E z))
      (ULift.up (F.vector z j))) :=
  (uliftFamily.{r} F).pairingMeasurable i j

theorem uliftFamily_dense_span (F : FundamentalFamily E) (z : Z) :
    (Submodule.span ℂ
      (range (fun i => (ULift.up (F.vector z i) : ULift.{r} (E z))))).topologicalClosure = ⊤ :=
  (uliftFamily.{r} F).dense z

@[simp] theorem uliftFamily_measurableSection_iff (F : FundamentalFamily E)
    (t : (z : Z) → ULift.{r} (E z)) :
    (uliftFamily F).IsMeasurableSection t ↔
      F.IsMeasurableSection (fun z => (t z).down) := Iff.rfl

theorem uliftFamily_measurableSection_up (F : FundamentalFamily E)
    (t : (z : Z) → E z) (ht : F.IsMeasurableSection t) :
    (uliftFamily.{r} F).IsMeasurableSection (fun z => ULift.up (t z)) := ht

@[simp] theorem uliftFamily_frame (F : FundamentalFamily E) (n : ℕ) (z : Z) :
    (uliftFamily.{r} F).frame n z = ULift.up (F.frame n z) :=
  frame_isometry (uliftUnitary (E z)).toLinearIsometry (F.vector z) n

@[simp] theorem uliftFamily_embedding (F : FundamentalFamily E) (z : Z) (x : E z) :
    (uliftFamily.{r} F).embedding z (ULift.up x) = F.embedding z x :=
  transportFamily_embedding F (fun z => uliftUnitary (E z)) z x

@[simp] theorem uliftFamily_embedding_down (F : FundamentalFamily E) (z : Z)
    (x : ULift.{r} (E z)) :
    (uliftFamily F).embedding z x = F.embedding z x.down := by
  cases x with
  | up x => exact uliftFamily_embedding F z x

theorem uliftFamily_embedding_eq (F : FundamentalFamily E) (z : Z) :
    (uliftFamily.{r} F).embedding z =
      (F.embedding z).comp (uliftUnitary (E z)).symm.toLinearIsometry := by
  apply LinearIsometry.ext
  intro x
  exact uliftFamily_embedding_down F z x

theorem uliftFamily_embedding_clm_eq (F : FundamentalFamily E) (z : Z) :
    ((uliftFamily.{r} F).embedding z).toContinuousLinearMap =
      (F.embedding z).toContinuousLinearMap.comp
        (uliftUnitary (E z)).symm.toLinearIsometry.toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  intro x
  exact uliftFamily_embedding_down F z x

@[simp] theorem uliftFamily_rangeProjection (F : FundamentalFamily E) (z : Z) :
    (uliftFamily.{r} F).rangeProjection z = F.rangeProjection z :=
  transportFamily_rangeProjection F (fun z => uliftUnitary (E z)) z

theorem uliftFamily_pullback (F : FundamentalFamily E)
    {H : Type*} [MeasurableSpace H] (f : H → Z) (hf : Measurable f) :
    uliftFamily.{r} (pullbackFamily F f hf) =
      pullbackFamily (uliftFamily.{r} F) f hf := rfl

variable {G : Z → Type w}
  [∀ z, NormedAddCommGroup (G z)] [∀ z, InnerProductSpace ℂ (G z)]
  [∀ z, CompleteSpace (G z)]

theorem uliftOperator_coefficientsMeasurable_iff (F : FundamentalFamily E)
    (Q : FundamentalFamily G) (T : (z : Z) → E z →L[ℂ] G z) :
    CoefficientsMeasurable (uliftFamily.{r} F) (uliftFamily.{s} Q)
      (fun z => uliftOperator.{r,s} (T z)) ↔ CoefficientsMeasurable F Q T := Iff.rfl

end FundamentalFields

section PhysicalWiring

variable (Ω : ℕ → Type u) [∀ n, MeasurableSpace (Ω n)]
  [∀ n, StandardBorelSpace (Ω n)] (D : PhysicalDomains Ω) (b : Bool)
  {E : (n : ℕ) → D.admissible n → Type v}
  [∀ n h, NormedAddCommGroup (E n h)] [∀ n h, InnerProductSpace ℂ (E n h)]
  [∀ n h, CompleteSpace (E n h)]
  (F : (n : ℕ) → FundamentalFamily (E n))
  {G : (n : ℕ) → D.actingDomain n b × Ω n → Type w}
  [∀ n z, NormedAddCommGroup (G n z)] [∀ n z, InnerProductSpace ℂ (G n z)]
  [∀ n z, CompleteSpace (G n z)]
  (Q : (n : ℕ) → FundamentalFamily (G n))
  (W : PhysicalMemoryWiring Ω D b F Q)

@[simp] theorem uliftWiring_acted_apply (n : ℕ) (h : D.successorDomain n b)
    (x : ULift.{s} (G n (D.successorOutcomePoint n b h))) :
    (uliftWiring.{r,s} Ω D b F Q W).acted n h x =
      ULift.up (W.acted n h x.down) := rfl

@[simp] theorem uliftWiring_acted_apply_up (n : ℕ) (h : D.successorDomain n b)
    (x : G n (D.successorOutcomePoint n b h)) :
    (uliftWiring.{r,s} Ω D b F Q W).acted n h (ULift.up x) =
      ULift.up (W.acted n h x) := rfl

@[simp] theorem uliftWiring_idle_apply (n : ℕ) (h : D.successorDomain n (!b))
    (x : ULift.{r} (E n (D.predecessorHistory n (!b) h))) :
    (uliftWiring.{r,s} Ω D b F Q W).idle n h x =
      ULift.up (W.idle n h x.down) := rfl

@[simp] theorem uliftWiring_idle_apply_up (n : ℕ) (h : D.successorDomain n (!b))
    (x : E n (D.predecessorHistory n (!b) h)) :
    (uliftWiring.{r,s} Ω D b F Q W).idle n h (ULift.up x) =
      ULift.up (W.idle n h x) := rfl

end PhysicalWiring

end QuantumProver.MatrixPhysicalUniverseHilbert
