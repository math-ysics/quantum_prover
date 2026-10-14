import QuantumProver.InformationTheory.ElegantJointMeasurement.RecordCoding
import QuantumProver.InformationTheory.ElegantJointMeasurement.TranscriptPOVM

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000

open MeasureTheory Set Function Filter

namespace QuantumProver.ElegantJointMeasurement.PhysicalTranscriptCoding

open QuantumProver.ElegantJointMeasurement.HilbertRecordCoding QuantumProver.ElegantJointMeasurement.HilbertTranscriptPOVM

universe u

variable (Ω : ℕ → Type u) [∀ n, MeasurableSpace (Ω n)]

abbrev PhysicalTranscript := (n : ℕ) → Ω n

def encodePhysicalTranscript (t : PhysicalTranscript Ω) :
    Transcript (CommonRecord Ω) :=
  fun n => encodeOutcome Ω n (t n)

@[simp] theorem encodePhysicalTranscript_apply
    (t : PhysicalTranscript Ω) (n : ℕ) :
    encodePhysicalTranscript Ω t n = encodeOutcome Ω n (t n) := rfl

theorem measurable_encodePhysicalTranscript :
    Measurable (encodePhysicalTranscript Ω) :=
  measurable_encodeTranscript Ω

theorem encodePhysicalTranscript_injective :
    Injective (encodePhysicalTranscript Ω) :=
  encodeTranscript_injective Ω

theorem measurableEmbedding_encodePhysicalTranscript
    [∀ n, StandardBorelSpace (Ω n)] :
    MeasurableEmbedding (encodePhysicalTranscript Ω) :=
  measurableEmbedding_encodeTranscript Ω

def prefixProjection (N : ℕ) (t : Transcript (CommonRecord Ω)) :
    QuantumProver.ElegantJointMeasurement.HilbertTranscriptPOVM.Prefix (CommonRecord Ω) N :=
  fun i => t i.val

theorem measurable_prefixProjection (N : ℕ) :
    Measurable (prefixProjection Ω N) :=
  Measurable.of_eval fun i => measurable_pi_apply i.val

theorem commonPrefix_eq_prefixProjection
    (t : Transcript (CommonRecord Ω)) (N : ℕ) :
    commonPrefix Ω t (N + 1) = prefixProjection Ω N t := by
  induction N with
  | zero =>
      funext i
      change t 0 = t i.val
      have hi : i.val = 0 :=
        Nat.eq_zero_of_le_zero (Finset.mem_Iic.mp i.property)
      rw [hi]
  | succ N ih =>
      change QuantumProver.ElegantJointMeasurement.HilbertSquareProcess.prefixStepEquiv N
          (commonPrefix Ω t (N + 1), t (N + 1)) =
        prefixProjection Ω (N + 1) t
      rw [ih]
      apply (QuantumProver.ElegantJointMeasurement.HilbertSquareProcess.prefixStepEquiv
        (R := CommonRecord Ω) N).symm.injective
      simp only [MeasurableEquiv.symm_apply_apply]
      apply Prod.ext <;> rfl

theorem encodePhysicalTranscript_prefix
    (t : PhysicalTranscript Ω) (N : ℕ) :
    prefixProjection Ω N (encodePhysicalTranscript Ω t) =
      encodeHistory Ω (N + 1) (roundPrefix Ω t (N + 1)) :=
  (commonPrefix_eq_prefixProjection Ω (encodePhysicalTranscript Ω t) N).symm.trans
    (encodeHistory_roundPrefix Ω t (N + 1)).symm

theorem encodePhysicalTranscript_prefixProjection
    (t : PhysicalTranscript Ω) (N : ℕ) :
    prefixProjection Ω N (encodePhysicalTranscript Ω t) =
      encodeHistory Ω (N + 1) (roundPrefix Ω t (N + 1)) :=
  encodePhysicalTranscript_prefix Ω t N

theorem encoded_prefix_map (μ : Measure (PhysicalTranscript Ω)) (N : ℕ) :
    (μ.map (encodePhysicalTranscript Ω)).map (prefixProjection Ω N) =
      (μ.map (fun t => roundPrefix Ω t (N + 1))).map
        (encodeHistory Ω (N + 1)) := by
  rw [Measure.map_map (measurable_prefixProjection Ω N)
      (measurable_encodePhysicalTranscript Ω),
    Measure.map_map (measurable_encodeHistory Ω (N + 1))
      (measurable_roundPrefix Ω (N + 1))]
  congr 1
  funext t
  exact encodePhysicalTranscript_prefix Ω t N

section Reports

variable [∀ n, StandardBorelSpace (Ω n)]

def liftPhysicalReport (J : PhysicalTranscript Ω → Fin 4) :
    Transcript (CommonRecord Ω) → Fin 4 :=
  liftTranscriptFunction Ω J 0

@[simp] theorem liftPhysicalReport_encode
    (J : PhysicalTranscript Ω → Fin 4) (t : PhysicalTranscript Ω) :
    liftPhysicalReport Ω J (encodePhysicalTranscript Ω t) = J t :=
  liftTranscriptFunction_encode Ω J 0 t

theorem liftPhysicalReport_comp_encode (J : PhysicalTranscript Ω → Fin 4) :
    liftPhysicalReport Ω J ∘ encodePhysicalTranscript Ω = J := by
  funext t
  exact liftPhysicalReport_encode Ω J t

theorem liftPhysicalReport_off_image (J : PhysicalTranscript Ω → Fin 4)
    (t : Transcript (CommonRecord Ω))
    (ht : t ∉ range (encodePhysicalTranscript Ω)) :
    liftPhysicalReport Ω J t = 0 := by
  unfold liftPhysicalReport liftTranscriptFunction
  exact dif_neg ht

theorem measurable_liftPhysicalReport
    (J : PhysicalTranscript Ω → Fin 4) (hJ : Measurable J) :
    Measurable (liftPhysicalReport Ω J) :=
  measurable_liftTranscriptFunction Ω J hJ 0

theorem liftPhysicalReport_event_preimage
    (J : PhysicalTranscript Ω → Fin 4) (s : Set (Fin 4)) :
    encodePhysicalTranscript Ω ⁻¹' (liftPhysicalReport Ω J ⁻¹' s) = J ⁻¹' s :=
  transcript_report_event_preimage Ω J 0 s

theorem liftPhysicalReport_event_probability
    (μ : Measure (PhysicalTranscript Ω))
    (J : PhysicalTranscript Ω → Fin 4) (s : Set (Fin 4)) :
    (μ.map (encodePhysicalTranscript Ω)) (liftPhysicalReport Ω J ⁻¹' s) =
      μ (J ⁻¹' s) := by
  rw [(measurableEmbedding_encodePhysicalTranscript Ω).map_apply,
    liftPhysicalReport_event_preimage]

theorem liftPhysicalReport_ae_congr
    (μ : Measure (PhysicalTranscript Ω))
    (J K : PhysicalTranscript Ω → Fin 4) (hJK : J =ᵐ[μ] K) :
    liftPhysicalReport Ω J =ᵐ[μ.map (encodePhysicalTranscript Ω)]
      liftPhysicalReport Ω K := by
  apply ae_iff.mpr
  rw [(measurableEmbedding_encodePhysicalTranscript Ω).map_apply]
  simpa only [Set.preimage_setOf_eq, liftPhysicalReport_encode] using ae_iff.mp hJK

theorem nullMeasurable_liftPhysicalReport
    (μ : Measure (PhysicalTranscript Ω))
    (J : PhysicalTranscript Ω → Fin 4) (hJ : NullMeasurable J μ) :
    NullMeasurable (liftPhysicalReport Ω J) (μ.map (encodePhysicalTranscript Ω)) := by
  have h : AEMeasurable J μ := hJ.aemeasurable
  have hEq := liftPhysicalReport_ae_congr Ω μ J (h.mk J) h.ae_eq_mk
  exact (measurable_liftPhysicalReport Ω (h.mk J) h.measurable_mk).nullMeasurable.congr
    hEq.symm

theorem completed_report_event_probability
    (μ : Measure (PhysicalTranscript Ω))
    (J : PhysicalTranscript Ω → Fin 4) (hJ : NullMeasurable J μ)
    (s : Set (Fin 4)) (hs : MeasurableSet s) :
    NullMeasurableSet (liftPhysicalReport Ω J ⁻¹' s)
        (μ.map (encodePhysicalTranscript Ω)) ∧
      (μ.map (encodePhysicalTranscript Ω)) (liftPhysicalReport Ω J ⁻¹' s) =
        μ (J ⁻¹' s) :=
  ⟨nullMeasurable_liftPhysicalReport Ω μ J hJ hs,
    liftPhysicalReport_event_probability Ω μ J s⟩

end Reports

end QuantumProver.ElegantJointMeasurement.PhysicalTranscriptCoding
