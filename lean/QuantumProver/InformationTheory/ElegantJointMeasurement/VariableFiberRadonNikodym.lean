import Mathlib
import QuantumProver.InformationTheory.ElegantJointMeasurement.ContinuousInstrumentRadonNikodym

noncomputable section
open MeasureTheory ProbabilityTheory Matrix Set Filter
open scoped ENNReal BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

set_option maxHeartbeats 800000

namespace QuantumProver.ElegantJointMeasurement.ContinuousInstrumentRadonNikodym
set_option maxHeartbeats 800000
variable {H Ω Q : Type*} [MeasurableSpace H] [MeasurableSpace Ω]
  [Fintype Q] [DecidableEq Q]

namespace PositiveChoiKernel
variable (C : PositiveChoiKernel (H := H) (Ω := Ω) (Q := Q))

theorem probe_isFinite_of_trace_le (d : ℝ)
    (hbound : ∀ h, (C.effect h univ).trace.re ≤ d)
    (v : Q → ℂ) : IsFiniteKernel (C.probe v) := by
  refine ⟨ENNReal.ofReal (‖quadraticCLM v‖ * d), ENNReal.ofReal_lt_top, ?_⟩
  intro h
  rw [C.probe_apply v h univ MeasurableSet.univ]
  apply ENNReal.ofReal_le_ofReal
  calc
    quadratic v (C.effect h univ) ≤ ‖quadraticCLM v (C.effect h univ)‖ := le_abs_self _
    _ ≤ ‖quadraticCLM v‖ * ‖C.effect h univ‖ := (quadraticCLM v).le_opNorm _
    _ ≤ ‖quadraticCLM v‖ * d := by
      gcongr
      exact (QuantumProver.ElegantJointMeasurement.ContinuousCPInstruments.posSemidef_norm_le_trace
        (C.effect h univ) (C.positive h univ MeasurableSet.univ)).trans (hbound h)

variable [MeasurableSpace.CountableOrCountablyGenerated H Ω]
variable [∀ v : Q → ℂ, IsFiniteKernel (C.probe v)]

def relativeProbeDensity (μ : Kernel H Ω) (v : Q → ℂ) (h : H) (ω : Ω) : ℝ :=
  ((C.probe v).rnDeriv μ h ω).toReal

@[fun_prop] theorem measurable_relativeProbeDensity (μ : Kernel H Ω) (v : Q → ℂ) :
    Measurable (fun z : H × Ω => C.relativeProbeDensity μ v z.1 z.2) := by
  exact ((C.probe v).measurable_rnDeriv μ).ennreal_toReal

theorem relativeProbeDensity_nonneg (μ : Kernel H Ω) (v : Q → ℂ) (h : H) (ω : Ω) :
    0 ≤ C.relativeProbeDensity μ v h ω := ENNReal.toReal_nonneg

theorem integrable_relativeProbeDensity (μ : Kernel H Ω) [IsFiniteKernel μ]
    (hAC : ∀ v h, C.probe v h ≪ μ h) (v : Q → ℂ) (h : H) :
    Integrable (C.relativeProbeDensity μ v h) (μ h) := by
  apply integrable_toReal_of_lintegral_ne_top
    (((C.probe v).measurable_rnDeriv μ).of_uncurry_left.aemeasurable)
  rw [Kernel.lintegral_rnDeriv (hAC v h)]
  exact measure_ne_top _ _

theorem setIntegral_relativeProbeDensity (μ : Kernel H Ω) [IsFiniteKernel μ]
    (hAC : ∀ v h, C.probe v h ≪ μ h) (v : Q → ℂ)
    (h : H) (s : Set Ω) (hs : MeasurableSet s) :
    (∫ ω in s, C.relativeProbeDensity μ v h ω ∂μ h) =
      quadratic v (C.effect h s) := by
  change (∫ ω in s, ((C.probe v).rnDeriv μ h ω).toReal
    ∂μ h) = _
  rw [integral_toReal
    (((C.probe v).measurable_rnDeriv μ).of_uncurry_left.aemeasurable.restrict)
    (ae_restrict_of_ae (Kernel.rnDeriv_lt_top (C.probe v) (μ)))]
  rw [Kernel.setLIntegral_rnDeriv (hAC v h) hs,
    C.probe_apply v h s hs, ENNReal.toReal_ofReal (quadratic_nonneg _ (C.positive h s hs) v)]

def relativeDensity (μ : Kernel H Ω) (h : H) (ω : Ω) : Matrix Q Q ℂ :=
  fun a b => polarizationEntry (fun v => C.relativeProbeDensity μ v h ω) a b

theorem measurable_relativeDensity (μ : Kernel H Ω) :
    Measurable (fun z : H × Ω => C.relativeDensity μ z.1 z.2) := by
  apply Measurable.of_eval
  intro a
  apply Measurable.of_eval
  intro b
  simp only [relativeDensity, polarizationEntry]
  fun_prop

theorem integrable_relativeDensity_entry (μ : Kernel H Ω) [IsFiniteKernel μ]
    (hAC : ∀ v h, C.probe v h ≪ μ h) (h : H) (a b : Q) :
    Integrable (fun ω => C.relativeDensity μ h ω a b) (μ h) := by
  have hp := C.integrable_relativeProbeDensity μ hAC
  exact (((hp (basisVector a + basisVector b) h).sub (hp (basisVector a) h)).sub
    (hp (basisVector b) h)).div_const 2 |>.ofReal |>.add
      ((((hp (basisVector a) h).add (hp (basisVector b) h)).sub
        (hp (basisVector a + Complex.I • basisVector b) h)).div_const 2 |>.ofReal
          |>.mul_const Complex.I)

theorem integrable_relativeDensity (μ : Kernel H Ω) [IsFiniteKernel μ]
    (hAC : ∀ v h, C.probe v h ≪ μ h) (h : H) :
    Integrable (C.relativeDensity μ h) (μ h) := by
  have heq : C.relativeDensity μ h = fun ω => ∑ a, ∑ b,
      C.relativeDensity μ h ω a b • Matrix.single a b 1 := by
    funext ω
    exact matrix_eq_sum_smul_single _
  rw [heq]
  exact integrable_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ =>
    (C.integrable_relativeDensity_entry μ hAC h a b).smul_const _

theorem setIntegral_relativeDensity_entry (μ : Kernel H Ω) [IsFiniteKernel μ]
    (hAC : ∀ v h, C.probe v h ≪ μ h) (h : H)
    (s : Set Ω) (hs : MeasurableSet s) (a b : Q) :
    (∫ ω in s, C.relativeDensity μ h ω a b ∂μ h) = C.effect h s a b := by
  change (∫ ω in s, polarizationEntry (fun v => C.relativeProbeDensity μ v h ω) a b
    ∂μ h) = _
  rw [integral_polarizationEntry _ _
    (fun v => (C.integrable_relativeProbeDensity μ hAC v h).integrableOn)]
  simp_rw [C.setIntegral_relativeProbeDensity μ hAC _ h s hs]
  exact polarization_quadratic _ (C.positive h s hs).isHermitian a b

theorem setIntegral_relativeDensity (μ : Kernel H Ω) [IsFiniteKernel μ]
    (hAC : ∀ v h, C.probe v h ≪ μ h) (h : H)
    (s : Set Ω) (hs : MeasurableSet s) :
    (∫ ω in s, C.relativeDensity μ h ω ∂μ h) = C.effect h s := by
  have heq : C.relativeDensity μ h = fun ω => ∑ a, ∑ b,
      C.relativeDensity μ h ω a b • Matrix.single a b 1 := by
    funext ω
    exact matrix_eq_sum_smul_single _
  rw [heq]
  calc
    _ = ∑ a, ∫ ω in s, (∑ b, C.relativeDensity μ h ω a b • Matrix.single a b (1 : ℂ))
        ∂μ h := integral_finsetSum _ fun a _ =>
          integrable_finsetSum _ fun b _ =>
            (C.integrable_relativeDensity_entry μ hAC h a b).integrableOn.smul_const _
    _ = ∑ a, ∑ b, (∫ ω in s, C.relativeDensity μ h ω a b ∂μ h) •
        Matrix.single a b (1 : ℂ) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [integral_finsetSum _ (fun b _ =>
        (C.integrable_relativeDensity_entry μ hAC h a b).integrableOn.smul_const _)]
      simp only [integral_smul_const]
    _ = C.effect h s := by
      simp_rw [C.setIntegral_relativeDensity_entry μ hAC h s hs]
      exact (matrix_eq_sum_smul_single _).symm

theorem ae_relativeDensity_isHermitian (μ : Kernel H Ω) [IsFiniteKernel μ]
    (hAC : ∀ v h, C.probe v h ≪ μ h) (h : H) :
    ∀ᵐ ω ∂μ h, (C.relativeDensity μ h ω).IsHermitian := by
  have hentry (a b : Q) : ∀ᵐ ω ∂μ h,
      star (C.relativeDensity μ h ω b a) = C.relativeDensity μ h ω a b := by
    have hstar : Integrable (fun ω => star (C.relativeDensity μ h ω b a))
        (μ h) :=
      (RCLike.conjLIE (K := ℂ)).toContinuousLinearEquiv.toContinuousLinearMap.integrable_comp
        (C.integrable_relativeDensity_entry μ hAC h b a)
    apply Integrable.ae_eq_of_forall_setIntegral_eq _ _ hstar
      (C.integrable_relativeDensity_entry μ hAC h a b)
    intro s hs _
    change (∫ ω in s, star (C.relativeDensity μ h ω b a) ∂μ h) = _
    erw [integral_conj, C.setIntegral_relativeDensity_entry μ hAC h s hs,
      C.setIntegral_relativeDensity_entry μ hAC h s hs]
    exact (C.positive h s hs).isHermitian.apply a b
  filter_upwards [ae_all_iff.mpr (fun a => ae_all_iff.mpr (hentry a))] with ω hω
  exact Matrix.IsHermitian.ext hω

theorem ae_relativeDensity_quadratic_nonneg (μ : Kernel H Ω) [IsFiniteKernel μ]
    (hAC : ∀ v h, C.probe v h ≪ μ h) (h : H) (v : Q → ℂ) :
    ∀ᵐ ω ∂μ h, 0 ≤ quadratic v (C.relativeDensity μ h ω) := by
  apply ae_nonneg_of_forall_setIntegral_nonneg
    ((quadraticCLM v).integrable_comp (C.integrable_relativeDensity μ hAC h))
  intro s hs _
  have hcomm := (quadraticCLM v).integral_comp_comm (μ := (μ h).restrict s)
    (C.integrable_relativeDensity μ hAC h).integrableOn
  change 0 ≤ ∫ ω in s, quadraticCLM v (C.relativeDensity μ h ω) ∂μ h
  rw [hcomm, C.setIntegral_relativeDensity μ hAC h s hs]
  exact quadratic_nonneg _ (C.positive h s hs) v

theorem ae_relativeDensity_posSemidef (μ : Kernel H Ω) [IsFiniteKernel μ]
    (hAC : ∀ v h, C.probe v h ≪ μ h) (h : H) :
    ∀ᵐ ω ∂μ h, (C.relativeDensity μ h ω).PosSemidef := by
  let u : ℕ → (Q → ℂ) := TopologicalSpace.denseSeq (Q → ℂ)
  have hu : DenseRange u := TopologicalSpace.denseRange_denseSeq _
  filter_upwards [C.ae_relativeDensity_isHermitian μ hAC h,
    ae_all_iff.mpr (fun n => C.ae_relativeDensity_quadratic_nonneg μ hAC h (u n))]
    with ω hherm hpos
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hherm
  intro v
  have hv : 0 ≤ quadratic v (C.relativeDensity μ h ω) := by
    apply hu.induction_on (p := fun x => 0 ≤ quadratic x (C.relativeDensity μ h ω)) v
    · apply isClosed_le continuous_const
      unfold quadratic
      simp only [dotProduct, Matrix.mulVec]
      fun_prop
    · exact hpos
  exact Complex.nonneg_iff.mpr ⟨hv,
    (hherm.im_star_dotProduct_mulVec_self v).symm⟩

def positiveRelativeDensity (μ : Kernel H Ω) (h : H) (ω : Ω) : Matrix Q Q ℂ :=
  by
    classical
    exact if (C.relativeDensity μ h ω).PosSemidef then C.relativeDensity μ h ω else 0

theorem measurable_positiveRelativeDensity (μ : Kernel H Ω) :
    Measurable (fun z : H × Ω => C.positiveRelativeDensity μ z.1 z.2) := by
  classical
  exact (C.measurable_relativeDensity μ).piecewise
    (Matrix.posSemidef_is_closed.measurableSet.preimage (C.measurable_relativeDensity μ)) measurable_const

theorem positiveRelativeDensity_posSemidef (μ : Kernel H Ω) (h : H) (ω : Ω) :
    (C.positiveRelativeDensity μ h ω).PosSemidef := by
  classical
  unfold positiveRelativeDensity
  split_ifs with hp
  · exact hp
  · exact Matrix.PosSemidef.zero

theorem positiveRelativeDensity_ae_eq (μ : Kernel H Ω) [IsFiniteKernel μ]
    (hAC : ∀ v h, C.probe v h ≪ μ h) (h : H) :
    C.positiveRelativeDensity μ h =ᵐ[μ h] C.relativeDensity μ h := by
  filter_upwards [C.ae_relativeDensity_posSemidef μ hAC h] with ω hω
  simp [positiveRelativeDensity, hω]

theorem integrable_positiveRelativeDensity (μ : Kernel H Ω) [IsFiniteKernel μ]
    (hAC : ∀ v h, C.probe v h ≪ μ h) (h : H) :
    Integrable (C.positiveRelativeDensity μ h) (μ h) :=
  (C.integrable_relativeDensity μ hAC h).congr (C.positiveRelativeDensity_ae_eq μ hAC h).symm

theorem setIntegral_positiveRelativeDensity (μ : Kernel H Ω) [IsFiniteKernel μ]
    (hAC : ∀ v h, C.probe v h ≪ μ h) (h : H)
    (s : Set Ω) (hs : MeasurableSet s) :
    (∫ ω in s, C.positiveRelativeDensity μ h ω ∂μ h) = C.effect h s := by
  rw [integral_congr_ae (ae_restrict_of_ae (C.positiveRelativeDensity_ae_eq μ hAC h))]
  exact C.setIntegral_relativeDensity μ hAC h s hs

theorem exists_joint_positive_density_relative (μ : Kernel H Ω) [IsFiniteKernel μ]
    (hAC : ∀ v h, C.probe v h ≪ μ h) :
    ∃ D : H → Ω → Matrix Q Q ℂ,
      Measurable (fun z : H × Ω => D z.1 z.2) ∧
      (∀ h ω, (D h ω).PosSemidef) ∧
      (∀ h, Integrable (D h) (μ h)) ∧
      (∀ h s, MeasurableSet s → (∫ ω in s, D h ω ∂μ h) = C.effect h s) := by
  exact ⟨C.positiveRelativeDensity μ, C.measurable_positiveRelativeDensity μ,
    C.positiveRelativeDensity_posSemidef μ,
    C.integrable_positiveRelativeDensity μ hAC,
    C.setIntegral_positiveRelativeDensity μ hAC⟩

end PositiveChoiKernel
end QuantumProver.ElegantJointMeasurement.ContinuousInstrumentRadonNikodym

namespace QuantumProver.ElegantJointMeasurement.ContinuousInstrumentRadonNikodym
namespace CountableReference
variable {H Ω : Type*} [MeasurableSpace H] [MeasurableSpace Ω]

def commonReference (κ : ℕ → Kernel H Ω) (d : ℝ) : Kernel H Ω where
  toFun h := (ENNReal.ofReal d)⁻¹ • Kernel.sum κ h
  measurable' := Measure.measurable_of_measurable_coe _ fun s hs => by
    simp only [Measure.smul_apply, smul_eq_mul]
    exact measurable_const.mul ((Kernel.sum κ).measurable_coe hs)

theorem commonReference_apply (κ : ℕ → Kernel H Ω) (d : ℝ)
    (h : H) (s : Set Ω) :
    commonReference κ d h s = (ENNReal.ofReal d)⁻¹ * Kernel.sum κ h s := by
  change ((ENNReal.ofReal d)⁻¹ • Kernel.sum κ h) s = _
  rw [Measure.smul_apply, smul_eq_mul]

theorem commonReference_isMarkov (κ : ℕ → Kernel H Ω) (d : ℝ) (hd : 0 < d)
    (htotal : ∀ h, Kernel.sum κ h univ = ENNReal.ofReal d) :
    IsMarkovKernel (commonReference κ d) := by
  constructor
  intro h
  constructor
  rw [commonReference_apply, htotal]
  exact ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.mpr hd).ne' ENNReal.ofReal_ne_top

theorem commonReference_scaled (κ : ℕ → Kernel H Ω) (d : ℝ) (hd : 0 < d)
    (h : H) :
    ENNReal.ofReal d • commonReference κ d h = Kernel.sum κ h := by
  change ENNReal.ofReal d • ((ENNReal.ofReal d)⁻¹ • Kernel.sum κ h) = _
  rw [smul_smul,
    ENNReal.mul_inv_cancel (ENNReal.ofReal_pos.mpr hd).ne' ENNReal.ofReal_ne_top,
    one_smul]

theorem component_absolutelyContinuous (κ : ℕ → Kernel H Ω) (d : ℝ)
    (p : ℕ) (h : H) : κ p h ≪ commonReference κ d h := by
  change κ p h ≪ (ENNReal.ofReal d)⁻¹ • Kernel.sum κ h
  have hs : κ p h ≪ Kernel.sum κ h := by
    rw [Kernel.sum_apply]
    exact Measure.absolutelyContinuous_sum_right p Measure.AbsolutelyContinuous.rfl
  exact hs.smul_right (c := (ENNReal.ofReal d)⁻¹)
    (ENNReal.inv_ne_zero.mpr ENNReal.ofReal_ne_top)

theorem component_mass_le (κ : ℕ → Kernel H Ω) (d : ℝ)
    (htotal : ∀ h, Kernel.sum κ h univ = ENNReal.ofReal d) (p : ℕ) (h : H) :
    κ p h univ ≤ ENNReal.ofReal d := by
  rw [← htotal h, Kernel.sum_apply' κ h MeasurableSet.univ]
  exact ENNReal.le_tsum (f := fun n => κ n h univ) p

theorem component_isFinite (κ : ℕ → Kernel H Ω) (d : ℝ)
    (htotal : ∀ h, Kernel.sum κ h univ = ENNReal.ofReal d) (p : ℕ) :
    IsFiniteKernel (κ p) :=
  ⟨ENNReal.ofReal d, ENNReal.ofReal_lt_top, component_mass_le κ d htotal p⟩

variable [MeasurableSpace.CountableOrCountablyGenerated H Ω]

def componentWeight (κ : ℕ → Kernel H Ω) (μ : Kernel H Ω)
    (p : ℕ) (h : H) (ω : Ω) : ℝ≥0∞ := (κ p).rnDeriv μ h ω

theorem measurable_componentWeight (κ : ℕ → Kernel H Ω) (μ : Kernel H Ω) (p : ℕ) :
    Measurable (fun z : H × Ω => componentWeight κ μ p z.1 z.2) :=
  (κ p).measurable_rnDeriv μ

theorem ae_sum_componentWeight (κ : ℕ → Kernel H Ω) (d : ℝ) (hd : 0 < d)
    (htotal : ∀ h, Kernel.sum κ h univ = ENNReal.ofReal d) (h : H) :
    ∀ᵐ ω ∂commonReference κ d h,
      (∑' p, componentWeight κ (commonReference κ d) p h ω) = ENNReal.ofReal d := by
  let μ := commonReference κ d
  letI : IsMarkovKernel μ := commonReference_isMarkov κ d hd htotal
  letI : ∀ p, IsFiniteKernel (κ p) := fun p => component_isFinite κ d htotal p
  have hwd (p : ℕ) : (μ h).withDensity (componentWeight κ μ p h) = κ p h := by
    change (μ h).withDensity ((κ p).rnDeriv μ h) = κ p h
    rw [← Kernel.withDensity_apply μ (measurable_componentWeight κ μ p) h]
    exact Kernel.withDensity_rnDeriv_eq (component_absolutelyContinuous κ d p h)
  have hm : Measurable (fun ω => ∑' p, componentWeight κ μ p h ω) :=
    Measurable.ennreal_tsum fun p =>
      (measurable_componentWeight κ μ p).of_uncurry_left
  have he : (μ h).withDensity (fun ω => ∑' p, componentWeight κ μ p h ω) =
      ENNReal.ofReal d • μ h := by
    calc
      _ = (μ h).withDensity (∑' p, componentWeight κ μ p h) := by
        congr 1
        funext ω
        exact (Pi.tsum_apply (Pi.summable.mpr fun _ => ENNReal.summable)).symm
      _ = Measure.sum (fun p => (μ h).withDensity (componentWeight κ μ p h)) :=
        withDensity_tsum fun p =>
          (measurable_componentWeight κ μ p).of_uncurry_left
      _ = Measure.sum (fun p => κ p h) := congrArg Measure.sum (funext hwd)
      _ = Kernel.sum κ h := (Kernel.sum_apply κ h).symm
      _ = _ := (commonReference_scaled κ d hd h).symm
  change ∀ᵐ ω ∂μ h, (∑' p, componentWeight κ μ p h ω) = ENNReal.ofReal d
  exact (withDensity_eq_iff_of_sigmaFinite hm.aemeasurable
    measurable_const.aemeasurable).mp (by rw [withDensity_const]; exact he)

theorem ae_sum_componentWeight_toReal (κ : ℕ → Kernel H Ω) (d : ℝ) (hd : 0 < d)
    (htotal : ∀ h, Kernel.sum κ h univ = ENNReal.ofReal d) (h : H) :
    ∀ᵐ ω ∂commonReference κ d h,
      (∑' p, (componentWeight κ (commonReference κ d) p h ω).toReal) = d := by
  let μ := commonReference κ d
  letI : IsMarkovKernel μ := commonReference_isMarkov κ d hd htotal
  letI : ∀ p, IsFiniteKernel (κ p) := fun p => component_isFinite κ d htotal p
  filter_upwards [ae_sum_componentWeight κ d hd htotal h,
    ae_all_iff.mpr (fun p => Kernel.rnDeriv_ne_top (κ p) μ)] with ω hsum hfinite
  have he := congrArg ENNReal.toReal hsum
  change (∑' p, (κ p).rnDeriv μ h ω).toReal = (ENNReal.ofReal d).toReal at he
  rw [ENNReal.tsum_toReal_eq hfinite, ENNReal.toReal_ofReal hd.le] at he
  exact he

end CountableReference

namespace PositiveChoiKernel
variable {H Ω Q : Type*} [MeasurableSpace H] [MeasurableSpace Ω]
  [Fintype Q] [DecidableEq Q]

theorem probe_absolutelyContinuous_trace
    (C : PositiveChoiKernel (H := H) (Ω := Ω) (Q := Q)) (v : Q → ℂ) (h : H) :
    C.probe v h ≪ C.traceKernel h := by
  have hc := C.probe_absolutelyContinuous 1 v h
  change C.probe v h ≪ (ENNReal.ofReal 1)⁻¹ • C.traceKernel h at hc
  simpa only [ENNReal.ofReal_one, inv_one, one_smul] using hc

end PositiveChoiKernel

namespace CountableChoi
variable {H Ω : Type*} [MeasurableSpace H] [MeasurableSpace Ω]
variable {Q : ℕ → Type*} [∀ p, Fintype (Q p)] [∀ p, DecidableEq (Q p)]
variable (C : ∀ p, PositiveChoiKernel (H := H) (Ω := Ω) (Q := Q p))

def commonReference (d : ℝ) : Kernel H Ω :=
  CountableReference.commonReference (fun p => (C p).traceKernel) d

theorem trace_bound (d : ℝ) (hd : 0 < d)
    (htotal : ∀ h, Kernel.sum (fun p => (C p).traceKernel) h univ = ENNReal.ofReal d)
    (p : ℕ) (h : H) : ((C p).effect h univ).trace.re ≤ d := by
  apply (ENNReal.ofReal_le_ofReal_iff hd.le).mp
  rw [← (C p).traceKernel_apply h univ MeasurableSet.univ]
  exact CountableReference.component_mass_le (fun p => (C p).traceKernel) d htotal p h

theorem probe_absolutelyContinuous_common (d : ℝ) (p : ℕ) (v : Q p → ℂ) (h : H) :
    (C p).probe v h ≪ commonReference C d h :=
  ((C p).probe_absolutelyContinuous_trace v h).trans
    (CountableReference.component_absolutelyContinuous (fun p => (C p).traceKernel) d p h)

variable [MeasurableSpace.CountableOrCountablyGenerated H Ω]

theorem exists_joint_component_densities (d : ℝ) (hd : 0 < d)
    (htotal : ∀ h, Kernel.sum (fun p => (C p).traceKernel) h univ = ENNReal.ofReal d) :
    ∃ D : (p : ℕ) → H → Ω → Matrix (Q p) (Q p) ℂ,
      (∀ p, Measurable (fun z : H × Ω => D p z.1 z.2)) ∧
      (∀ p h ω, (D p h ω).PosSemidef) ∧
      (∀ p h, Integrable (D p h) (commonReference C d h)) ∧
      (∀ p h s, MeasurableSet s →
        (∫ ω in s, D p h ω ∂commonReference C d h) = (C p).effect h s) := by
  let μ := commonReference C d
  letI : IsMarkovKernel μ :=
    CountableReference.commonReference_isMarkov (fun p => (C p).traceKernel) d hd htotal
  letI : ∀ p (v : Q p → ℂ), IsFiniteKernel ((C p).probe v) := fun p v =>
    (C p).probe_isFinite_of_trace_le d (trace_bound C d hd htotal p) v
  refine ⟨fun p => (C p).positiveRelativeDensity μ, ?_, ?_, ?_, ?_⟩
  · intro p
    exact (C p).measurable_positiveRelativeDensity μ
  · intro p h ω
    exact (C p).positiveRelativeDensity_posSemidef μ h ω
  · intro p h
    exact (C p).integrable_positiveRelativeDensity μ
      (probe_absolutelyContinuous_common C d p) h
  · intro p h s hs
    exact (C p).setIntegral_positiveRelativeDensity μ
      (probe_absolutelyContinuous_common C d p) h s hs

end CountableChoi
end QuantumProver.ElegantJointMeasurement.ContinuousInstrumentRadonNikodym

namespace QuantumProver.ElegantJointMeasurement.ContinuousInstrumentRadonNikodym
namespace CP
variable {H Ω I O : Type*} [MeasurableSpace H] [MeasurableSpace Ω]
  [Fintype I] [DecidableEq I] [Fintype O] [DecidableEq O]

structure MatrixCPComponent where
  map : H → Set Ω → (Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ)
  empty : ∀ h, map h ∅ = 0
  completelyPositive : ∀ h s, MeasurableSet s → QuantumProver.ElegantJointMeasurement.CP.CompletelyPositive (map h s)
  measurable_entry : ∀ s, MeasurableSet s → ∀ i j b c,
    Measurable (fun h => map h s (Matrix.single i j 1) b c)
  coordinate_additive : ∀ h (s : ℕ → Set Ω), (∀ n, MeasurableSet (s n)) →
    Pairwise (fun i j => Disjoint (s i) (s j)) → ∀ i j b c,
      HasSum (fun n => map h (s n) (Matrix.single i j 1) b c)
        (map h (⋃ n, s n) (Matrix.single i j 1) b c)

namespace MatrixCPComponent
variable (P : MatrixCPComponent (H := H) (Ω := Ω) (I := I) (O := O))

def choiKernel : CoordinateChoiKernel (H := H) (Ω := Ω) (Q := I × O) where
  effect h s := QuantumProver.ElegantJointMeasurement.CP.choi (P.map h s)
  empty h := by
    ext a b
    change P.map h ∅ (Matrix.single a.1 b.1 1) a.2 b.2 = 0
    rw [P.empty]
    rfl
  positive h s hs := QuantumProver.ElegantJointMeasurement.CP.choi_posSemidef _ (P.completelyPositive h s hs)
  measurable_entry s hs a b := P.measurable_entry s hs a.1 b.1 a.2 b.2
  coordinate_additive h s hs hdisj a b :=
    P.coordinate_additive h s hs hdisj a.1 b.1 a.2 b.2

theorem map_eq_zero_of_emptyOutput [IsEmpty O] (h : H) (s : Set Ω) : P.map h s = 0 := by
  apply LinearMap.ext
  intro X
  ext b c
  exact isEmptyElim b

end MatrixCPComponent

structure MatrixVaryingCPInstrument where
  outputTag : H × Ω → ℕ
  measurable_outputTag : Measurable outputTag
  component : (p : ℕ) → MatrixCPComponent (H := H) (Ω := Ω) (I := I) (O := Fin p)
  traceComplete : ∀ h X, HasSum (fun p => ((component p).map h univ X).trace) X.trace
  component_supported : ∀ p h,
    (component p).map h {ω | outputTag (h,ω) ≠ p} = 0

namespace MatrixVaryingCPInstrument
variable (P : MatrixVaryingCPInstrument (H := H) (Ω := Ω) (I := I))

def componentChoi (p : ℕ) : PositiveChoiKernel (H := H) (Ω := Ω) (Q := I × Fin p) :=
  (P.component p).choiKernel.toPositiveChoiKernel

theorem total_component_trace_mass (h : H) :
    Kernel.sum (fun p => (P.componentChoi p).traceKernel) h univ =
      ENNReal.ofReal (Fintype.card I : ℝ) := by
  have hs : HasSum (fun p => ((P.componentChoi p).effect h univ).trace.re)
      (Fintype.card I : ℝ) := by
    have ht := Complex.hasSum_re (P.traceComplete h (1 : Matrix I I ℂ))
    change HasSum (fun p => (QuantumProver.ElegantJointMeasurement.CP.choi ((P.component p).map h univ)).trace.re)
      (Fintype.card I : ℝ)
    simpa only [QuantumProver.ElegantJointMeasurement.ContinuousCPInstruments.choi_trace,
      Matrix.trace_one, Complex.natCast_re] using ht
  have hn (p : ℕ) : 0 ≤ ((P.componentChoi p).effect h univ).trace.re :=
    (norm_nonneg _).trans (QuantumProver.ElegantJointMeasurement.ContinuousCPInstruments.posSemidef_norm_le_trace _
      ((P.componentChoi p).positive h univ MeasurableSet.univ))
  rw [Kernel.sum_apply' _ _ MeasurableSet.univ]
  have he (p : ℕ) : (P.componentChoi p).traceKernel h univ =
      ENNReal.ofReal ((P.componentChoi p).effect h univ).trace.re :=
    (P.componentChoi p).traceKernel_apply h univ MeasurableSet.univ
  simp_rw [he]
  rw [← ENNReal.ofReal_tsum_of_nonneg hn hs.summable, hs.tsum_eq]

def commonReference : Kernel H Ω :=
  CountableChoi.commonReference P.componentChoi (Fintype.card I)

variable [Nonempty I]

instance commonReference_isMarkov : IsMarkovKernel P.commonReference :=
  CountableReference.commonReference_isMarkov _ (Fintype.card I)
    (by exact_mod_cast Fintype.card_pos (α := I)) P.total_component_trace_mass

theorem component_probe_finite (p : ℕ) (v : I × Fin p → ℂ) :
    IsFiniteKernel ((P.componentChoi p).probe v) :=
  (P.componentChoi p).probe_isFinite_of_trace_le (Fintype.card I)
    (CountableChoi.trace_bound P.componentChoi (Fintype.card I)
      (by exact_mod_cast Fintype.card_pos (α := I)) P.total_component_trace_mass p) v

theorem component_probe_absolutelyContinuous (p : ℕ) (v : I × Fin p → ℂ) (h : H) :
    (P.componentChoi p).probe v h ≪ P.commonReference h :=
  CountableChoi.probe_absolutelyContinuous_common P.componentChoi (Fintype.card I) p v h

variable [MeasurableSpace.CountableOrCountablyGenerated H Ω]

def componentDensity (p : ℕ) (h : H) (ω : Ω) :
    Matrix I I ℂ →ₗ[ℂ] Matrix (Fin p) (Fin p) ℂ :=
  fromChoi ((P.componentChoi p).positiveRelativeDensity P.commonReference h ω)

theorem componentDensity_completelyPositive (p : ℕ) (h : H) (ω : Ω) :
    QuantumProver.ElegantJointMeasurement.CP.CompletelyPositive (P.componentDensity p h ω) := by
  letI : ∀ v : I × Fin p → ℂ, IsFiniteKernel ((P.componentChoi p).probe v) :=
    P.component_probe_finite p
  exact fromChoi_completelyPositive _
    ((P.componentChoi p).positiveRelativeDensity_posSemidef P.commonReference h ω)

theorem componentDensity_joint_coordinate_measurable (p : ℕ)
    (i j : I) (b c : Fin p) :
    Measurable (fun z : H × Ω => P.componentDensity p z.1 z.2 (Matrix.single i j 1) b c) := by
  letI : ∀ v : I × Fin p → ℂ, IsFiniteKernel ((P.componentChoi p).probe v) :=
    P.component_probe_finite p
  simp only [componentDensity, fromChoi_matrix_unit]
  exact (measurable_pi_iff.mp (measurable_pi_iff.mp
    ((P.componentChoi p).measurable_positiveRelativeDensity P.commonReference) (i,b))) (j,c)

theorem componentDensity_integrable (p : ℕ) (h : H) (X : Matrix I I ℂ) :
    Integrable (fun ω => P.componentDensity p h ω X) (P.commonReference h) := by
  letI : IsMarkovKernel P.commonReference := P.commonReference_isMarkov
  letI : ∀ v : I × Fin p → ℂ, IsFiniteKernel ((P.componentChoi p).probe v) :=
    P.component_probe_finite p
  exact (choiReadoutCLM (I := I) (O := Fin p) X).integrable_comp
    ((P.componentChoi p).integrable_positiveRelativeDensity P.commonReference
      (P.component_probe_absolutelyContinuous p) h)

theorem componentDensity_setIntegral (p : ℕ) (h : H) (s : Set Ω)
    (hs : MeasurableSet s) (X : Matrix I I ℂ) :
    (∫ ω in s, P.componentDensity p h ω X ∂P.commonReference h) =
      (P.component p).map h s X := by
  letI : IsMarkovKernel P.commonReference := P.commonReference_isMarkov
  letI : ∀ v : I × Fin p → ℂ, IsFiniteKernel ((P.componentChoi p).probe v) :=
    P.component_probe_finite p
  have hcomm := (choiReadoutCLM X).integral_comp_comm
    (μ := (P.commonReference h).restrict s)
    ((P.componentChoi p).integrable_positiveRelativeDensity P.commonReference
      (P.component_probe_absolutelyContinuous p) h).integrableOn
  change (∫ ω in s, choiReadoutCLM X
    ((P.componentChoi p).positiveRelativeDensity P.commonReference h ω)
      ∂P.commonReference h) = _
  rw [hcomm, (P.componentChoi p).setIntegral_positiveRelativeDensity P.commonReference
    (P.component_probe_absolutelyContinuous p) h s hs]
  change fromChoi (QuantumProver.ElegantJointMeasurement.CP.choi ((P.component p).map h s)) X = _
  rw [fromChoi_choi]

theorem zero_component_map (h : H) (s : Set Ω) : (P.component 0).map h s = 0 :=
  (P.component 0).map_eq_zero_of_emptyOutput h s

end MatrixVaryingCPInstrument
end CP
end QuantumProver.ElegantJointMeasurement.ContinuousInstrumentRadonNikodym

namespace QuantumProver.ElegantJointMeasurement.ContinuousInstrumentRadonNikodym
namespace PositiveChoiKernel
variable {H Ω Q : Type*} [MeasurableSpace H] [MeasurableSpace Ω]
  [Fintype Q] [DecidableEq Q]
variable [MeasurableSpace.CountableOrCountablyGenerated H Ω]
variable (C : PositiveChoiKernel (H := H) (Ω := Ω) (Q := Q))
variable [∀ v : Q → ℂ, IsFiniteKernel (C.probe v)]

instance traceKernel_isFinite_of_probes : IsFiniteKernel C.traceKernel := by
  refine ⟨∑ a, (C.probe (basisVector a)).bound,
    ENNReal.sum_lt_top.mpr (fun a _ => (C.probe (basisVector a)).bound_lt_top), ?_⟩
  intro h
  rw [traceKernel, Kernel.finsetSum_apply']
  exact Finset.sum_le_sum fun a _ => (C.probe (basisVector a)).measure_le_bound h univ

theorem traceKernel_absolutelyContinuous (μ : Kernel H Ω)
    (hAC : ∀ v h, C.probe v h ≪ μ h) (h : H) : C.traceKernel h ≪ μ h := by
  refine Measure.AbsolutelyContinuous.mk fun s hs hzero => ?_
  rw [traceKernel, Kernel.finsetSum_apply']
  exact Finset.sum_eq_zero fun a _ => hAC (basisVector a) h hzero

def relativeTraceWeight (μ : Kernel H Ω) (h : H) (ω : Ω) : ℝ :=
  (C.traceKernel.rnDeriv μ h ω).toReal

theorem relativeDensity_trace_ae_eq (μ : Kernel H Ω) [IsFiniteKernel μ]
    (hAC : ∀ v h, C.probe v h ≪ μ h) (h : H) :
    (fun ω => (C.positiveRelativeDensity μ h ω).trace.re) =ᵐ[μ h]
      C.relativeTraceWeight μ h := by
  letI : IsFiniteKernel C.traceKernel := C.traceKernel_isFinite_of_probes
  have hd : Integrable (fun ω => (C.positiveRelativeDensity μ h ω).trace.re) (μ h) := by
    simpa only [traceReCLM_apply] using
      (traceReCLM (Q := Q)).integrable_comp
        (C.integrable_positiveRelativeDensity μ hAC h)
  have hw : Integrable (C.relativeTraceWeight μ h) (μ h) := by
    apply integrable_toReal_of_lintegral_ne_top
      ((C.traceKernel.measurable_rnDeriv μ).of_uncurry_left.aemeasurable)
    rw [Kernel.lintegral_rnDeriv (C.traceKernel_absolutelyContinuous μ hAC h)]
    exact measure_ne_top _ _
  apply Integrable.ae_eq_of_forall_setIntegral_eq _ _ hd hw
  intro s hs _
  have hwset : (∫ ω in s, C.relativeTraceWeight μ h ω ∂μ h) =
      (C.effect h s).trace.re := by
    change (∫ ω in s, (C.traceKernel.rnDeriv μ h ω).toReal ∂μ h) = _
    rw [integral_toReal
      ((C.traceKernel.measurable_rnDeriv μ).of_uncurry_left.aemeasurable.restrict)
      (ae_restrict_of_ae (Kernel.rnDeriv_lt_top C.traceKernel μ)),
      Kernel.setLIntegral_rnDeriv (C.traceKernel_absolutelyContinuous μ hAC h) hs,
      C.traceKernel_apply h s hs,
      ENNReal.toReal_ofReal ((norm_nonneg _).trans
        (QuantumProver.ElegantJointMeasurement.ContinuousCPInstruments.posSemidef_norm_le_trace _ (C.positive h s hs)))]
  simp only [← traceReCLM_apply]
  rw [(traceReCLM (Q := Q)).integral_comp_comm
      (C.integrable_positiveRelativeDensity μ hAC h).integrableOn,
    C.setIntegral_positiveRelativeDensity μ hAC h s hs, traceReCLM_apply]
  exact hwset.symm

theorem positiveRelativeDensity_zero_on_set (μ : Kernel H Ω) [IsFiniteKernel μ]
    (hAC : ∀ v h, C.probe v h ≪ μ h) (h : H)
    (s : Set Ω) (hs : MeasurableSet s) (hzero : C.effect h s = 0) :
    ∀ᵐ ω ∂μ h, ω ∈ s → C.positiveRelativeDensity μ h ω = 0 := by
  have hd := C.integrable_positiveRelativeDensity μ hAC h
  have ht : Integrable (fun ω => (C.positiveRelativeDensity μ h ω).trace.re)
      ((μ h).restrict s) := by
    simpa only [traceReCLM_apply] using
      (traceReCLM (Q := Q)).integrable_comp hd.integrableOn
  have hn (ω : Ω) : 0 ≤ (C.positiveRelativeDensity μ h ω).trace.re :=
    (norm_nonneg _).trans (QuantumProver.ElegantJointMeasurement.ContinuousCPInstruments.posSemidef_norm_le_trace _
      (C.positiveRelativeDensity_posSemidef μ h ω))
  have hi : (∫ ω in s, (C.positiveRelativeDensity μ h ω).trace.re ∂μ h) = 0 := by
    simp only [← traceReCLM_apply]
    rw [(traceReCLM (Q := Q)).integral_comp_comm hd.integrableOn,
      C.setIntegral_positiveRelativeDensity μ hAC h s hs, hzero]
    simp
  have hz := (integral_eq_zero_iff_of_nonneg hn ht).mp hi
  apply (ae_restrict_iff' hs).mp
  filter_upwards [hz] with ω hω
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg _)
  simpa only [hω, Pi.zero_apply] using QuantumProver.ElegantJointMeasurement.ContinuousCPInstruments.posSemidef_norm_le_trace _
    (C.positiveRelativeDensity_posSemidef μ h ω)

end PositiveChoiKernel

namespace CountableGram
variable {Ω I : Type*} [MeasurableSpace Ω] [Fintype I] [DecidableEq I]

def tracePairing (X : Matrix I I ℂ) : Matrix I I ℂ →L[ℂ] ℂ :=
  ({ toFun := fun G => (G * X).trace
     map_add' := by intro A B; simp [Matrix.add_mul, Matrix.trace_add]
     map_smul' := by intro z A; simp [Matrix.trace_smul] } :
    Matrix I I ℂ →ₗ[ℂ] ℂ).toContinuousLinearMap

theorem hasSum_integral_gram_eq_one (μ : Measure Ω) (G : ℕ → Ω → Matrix I I ℂ)
    (hG : ∀ p, Integrable (G p) μ) (hpos : ∀ p ω, (G p ω).PosSemidef)
    (represented_hmatrix : ∀ X, HasSum (fun p => ((∫ ω, G p ω ∂μ) * X).trace) X.trace) :
    HasSum (fun p => ∫ ω, G p ω ∂μ) (1 : Matrix I I ℂ) := by
  let M (p : ℕ) := ∫ ω, G p ω ∂μ
  have ht : HasSum (fun p => (M p).trace.re) ((1 : Matrix I I ℂ).trace.re) := by
    simpa only [M, Matrix.mul_one] using Complex.hasSum_re (represented_hmatrix 1)
  have hnorm (p : ℕ) : ‖M p‖ ≤ (M p).trace.re := by
    have htrace : Integrable (fun ω => (G p ω).trace.re) μ := by
      simpa only [traceReCLM_apply] using
        (traceReCLM (Q := I)).integrable_comp (hG p)
    have he : (∫ ω, (G p ω).trace.re ∂μ) = (M p).trace.re := by
      simpa only [traceReCLM_apply] using
        (traceReCLM (Q := I)).integral_comp_comm (hG p)
    calc
      ‖M p‖ ≤ ∫ ω, ‖G p ω‖ ∂μ := norm_integral_le_integral_norm _
      _ ≤ ∫ ω, (G p ω).trace.re ∂μ := integral_mono (hG p).norm htrace
        (fun ω => QuantumProver.ElegantJointMeasurement.ContinuousCPInstruments.posSemidef_norm_le_trace _ (hpos p ω))
      _ = _ := he
  have hm : Summable M := ht.summable.of_norm_bounded hnorm
  have hsum : (∑' p, M p) = (1 : Matrix I I ℂ) := by
    apply Matrix.ext_iff_trace_mul_right.mpr
    intro X
    have hx := (tracePairing X).hasSum hm.hasSum
    have he := hx.unique (represented_hmatrix X)
    change ((∑' p, M p) * X).trace = X.trace at he
    simpa only [Matrix.one_mul] using he
  exact hsum ▸ hm.hasSum

end CountableGram
end QuantumProver.ElegantJointMeasurement.ContinuousInstrumentRadonNikodym

namespace QuantumProver.ElegantJointMeasurement.ContinuousInstrumentRadonNikodym
namespace CountableGram
variable {Ω I O : Type*} [MeasurableSpace Ω]
  [Fintype I] [DecidableEq I] [Fintype O] [DecidableEq O]

theorem integrable_canonicalGram_of_integrable_identity_action
    (μ : Measure Ω) (Φ : Ω → (Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ))
    (hΦ : QuantumProver.ElegantJointMeasurement.ContinuousCPInstruments.CoordinateMeasurable Φ)
    (hCP : ∀ ω, QuantumProver.ElegantJointMeasurement.CP.CompletelyPositive (Φ ω))
    (hidentity : Integrable (fun ω => Φ ω 1) μ) :
    Integrable (QuantumProver.ElegantJointMeasurement.ContinuousCPInstruments.canonicalGram Φ) μ := by
  have hm : Integrable (fun ω => (Φ ω 1).trace.re) μ := by
    simpa only [traceReCLM_apply] using
      (traceReCLM (Q := O)).integrable_comp hidentity
  apply hm.mono'
    (QuantumProver.ElegantJointMeasurement.ContinuousCPInstruments.measurable_canonicalGram Φ hΦ).stronglyMeasurable.aestronglyMeasurable
  exact Filter.Eventually.of_forall fun ω => by
    simpa only [QuantumProver.ElegantJointMeasurement.ContinuousCPInstruments.canonicalGram_trace Φ hCP ω] using
      QuantumProver.ElegantJointMeasurement.ContinuousCPInstruments.posSemidef_norm_le_trace _
        (QuantumProver.ElegantJointMeasurement.ContinuousCPInstruments.canonicalGram_posSemidef Φ ω)

end CountableGram

namespace CP.MatrixVaryingCPInstrument
variable {H Ω I : Type*} [MeasurableSpace H] [MeasurableSpace Ω]
  [Fintype I] [DecidableEq I] [Nonempty I]
  [MeasurableSpace.CountableOrCountablyGenerated H Ω]
variable (P : MatrixVaryingCPInstrument (H := H) (Ω := Ω) (I := I))

theorem componentDensity_coordinateMeasurable (p : ℕ) (h : H) :
    QuantumProver.ElegantJointMeasurement.ContinuousCPInstruments.CoordinateMeasurable (P.componentDensity p h) := by
  intro i j b c
  exact Measurable.of_uncurry_left
    (f := fun h' : H => fun ω : Ω =>
      P.componentDensity p h' ω (Matrix.single i j (1 : ℂ)) b c)
    (x := h) (P.componentDensity_joint_coordinate_measurable p i j b c)

def componentGram (p : ℕ) (h : H) (ω : Ω) : Matrix I I ℂ :=
  QuantumProver.ElegantJointMeasurement.ContinuousCPInstruments.canonicalGram (P.componentDensity p h) ω

theorem componentGram_integrable (p : ℕ) (h : H) :
    Integrable (P.componentGram p h) (P.commonReference h) :=
  CountableGram.integrable_canonicalGram_of_integrable_identity_action _ _
    (P.componentDensity_coordinateMeasurable p h)
    (P.componentDensity_completelyPositive p h)
    (P.componentDensity_integrable p h 1)

theorem componentGram_integral_trace (p : ℕ) (h : H) (X : Matrix I I ℂ) :
    ((∫ ω, P.componentGram p h ω ∂P.commonReference h) * X).trace =
      ((P.component p).map h univ X).trace := by
  let T : Matrix (Fin p) (Fin p) ℂ →L[ℂ] ℂ :=
    LinearMap.toContinuousLinearMap (Matrix.traceLinearMap (Fin p) ℂ ℂ)
  have hG := (CountableGram.tracePairing X).integral_comp_comm (P.componentGram_integrable p h)
  have hT := T.integral_comp_comm (P.componentDensity_integrable p h X)
  have hrecover : (∫ ω, P.componentDensity p h ω X ∂P.commonReference h) =
      (P.component p).map h univ X := by
    simpa only [Measure.restrict_univ] using
      P.componentDensity_setIntegral p h univ MeasurableSet.univ X
  calc
    _ = ∫ ω, (P.componentGram p h ω * X).trace ∂P.commonReference h := hG.symm
    _ = ∫ ω, (P.componentDensity p h ω X).trace ∂P.commonReference h := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun ω =>
        (QuantumProver.ElegantJointMeasurement.ContinuousCPInstruments.matrix_trace_eq_canonicalGram
          (P.componentDensity p h) (P.componentDensity_completelyPositive p h) ω X).symm
    _ = (∫ ω, P.componentDensity p h ω X ∂P.commonReference h).trace := hT
    _ = _ := congrArg Matrix.trace hrecover

theorem hasSum_integral_componentGram (h : H) :
    HasSum (fun p => ∫ ω, P.componentGram p h ω ∂P.commonReference h)
      (1 : Matrix I I ℂ) := by
  apply CountableGram.hasSum_integral_gram_eq_one
    (P.commonReference h) (fun p => P.componentGram p h)
    (fun p => P.componentGram_integrable p h)
    (fun p ω => QuantumProver.ElegantJointMeasurement.ContinuousCPInstruments.canonicalGram_posSemidef _ ω)
  intro X
  exact (P.traceComplete h X).congr_fun fun p =>
    P.componentGram_integral_trace p h X

abbrev HiddenColumn (I : Type*) := Σ p : ℕ, I × Fin p

def hiddenGram (z : H × Ω) (q : HiddenColumn I) : Matrix I I ℂ :=
  let K := QuantumProver.ElegantJointMeasurement.ContinuousCPInstruments.canonicalKraus (P.componentDensity q.1 z.1) z.2 q.2
  Kᴴ * K

variable [MeasurableSpace I] [MeasurableSingletonClass I]

instance hiddenColumn_measurableSingletonClass : MeasurableSingletonClass (HiddenColumn I) := by
  constructor
  intro q
  change MeasurableSet[⨅ p : ℕ,
    (inferInstance : MeasurableSpace (I × Fin p)).map (Sigma.mk p)] {q}
  rw [MeasurableSpace.measurableSet_iInf]
  intro p
  change MeasurableSet ((Sigma.mk p) ⁻¹' ({q} : Set (HiddenColumn I)))
  exact (Set.to_countable _).measurableSet

theorem measurable_hiddenGram : Measurable (fun z : (H × Ω) × HiddenColumn I =>
    P.hiddenGram z.1 z.2) := by
  apply measurable_from_prod_countable_left
  intro q
  let Φ (z : H × Ω) := P.componentDensity q.1 z.1 z.2
  have hΦ : QuantumProver.ElegantJointMeasurement.ContinuousCPInstruments.CoordinateMeasurable Φ :=
    P.componentDensity_joint_coordinate_measurable q.1
  have hK := QuantumProver.ElegantJointMeasurement.ContinuousCPInstruments.measurable_canonicalKraus Φ hΦ q.2
  have he : ∀ b i, Measurable (fun z : H × Ω =>
      QuantumProver.ElegantJointMeasurement.ContinuousCPInstruments.canonicalKraus Φ z q.2 b i) := fun b i =>
    (measurable_pi_apply i).comp ((measurable_pi_apply b).comp hK)
  refine Measurable.of_eval fun i => Measurable.of_eval fun j => ?_
  simp only [hiddenGram, Matrix.mul_apply, Matrix.conjTranspose_apply]
  change Measurable (fun z : H × Ω => ∑ b : Fin q.1,
    star (QuantumProver.ElegantJointMeasurement.ContinuousCPInstruments.canonicalKraus Φ z q.2 b i) *
      QuantumProver.ElegantJointMeasurement.ContinuousCPInstruments.canonicalKraus Φ z q.2 b j)
  exact Finset.measurable_sum Finset.univ fun b _ =>
    (continuous_star.measurable.comp (he b i)).mul (he b j)

end CP.MatrixVaryingCPInstrument
end QuantumProver.ElegantJointMeasurement.ContinuousInstrumentRadonNikodym

namespace QuantumProver.ElegantJointMeasurement.ContinuousInstrumentRadonNikodym
namespace CP.MatrixVaryingCPInstrument
variable {H Ω I : Type*} [MeasurableSpace H] [MeasurableSpace Ω]
  [Fintype I] [DecidableEq I] [Nonempty I]
  [MeasurableSpace.CountableOrCountablyGenerated H Ω]
variable (P : MatrixVaryingCPInstrument (H := H) (Ω := Ω) (I := I))

def componentChoiDensity (p : ℕ) (z : H × Ω) : Matrix (I × Fin p) (I × Fin p) ℂ :=
  (P.componentChoi p).positiveRelativeDensity P.commonReference z.1 z.2

theorem measurable_componentChoiDensity (p : ℕ) : Measurable (P.componentChoiDensity p) := by
  letI : ∀ v : I × Fin p → ℂ, IsFiniteKernel ((P.componentChoi p).probe v) :=
    P.component_probe_finite p
  exact (P.componentChoi p).measurable_positiveRelativeDensity P.commonReference

theorem componentChoiDensity_trace_ae_eq (p : ℕ) (h : H) :
    (fun ω => (P.componentChoiDensity p (h,ω)).trace.re) =ᵐ[P.commonReference h]
      (fun ω => ((P.componentChoi p).traceKernel.rnDeriv P.commonReference h ω).toReal) := by
  letI : IsMarkovKernel P.commonReference := P.commonReference_isMarkov
  letI : ∀ v : I × Fin p → ℂ, IsFiniteKernel ((P.componentChoi p).probe v) :=
    P.component_probe_finite p
  exact (P.componentChoi p).relativeDensity_trace_ae_eq P.commonReference
    (P.component_probe_absolutelyContinuous p) h

theorem componentChoiDensity_off_tag (p : ℕ) (h : H) :
    ∀ᵐ ω ∂P.commonReference h,
      P.outputTag (h,ω) ≠ p → P.componentChoiDensity p (h,ω) = 0 := by
  letI : IsMarkovKernel P.commonReference := P.commonReference_isMarkov
  letI : ∀ v : I × Fin p → ℂ, IsFiniteKernel ((P.componentChoi p).probe v) :=
    P.component_probe_finite p
  have hs : MeasurableSet {ω | P.outputTag (h,ω) ≠ p} :=
    ((measurableSet_singleton p).preimage
      (Measurable.of_uncurry_left (f := fun h' ω => P.outputTag (h',ω))
        (x := h) P.measurable_outputTag)).compl
  have hz : (P.componentChoi p).effect h {ω | P.outputTag (h,ω) ≠ p} = 0 := by
    change QuantumProver.ElegantJointMeasurement.CP.choi ((P.component p).map h {ω | P.outputTag (h,ω) ≠ p}) = 0
    rw [P.component_supported]
    ext a b
    rfl
  exact (P.componentChoi p).positiveRelativeDensity_zero_on_set P.commonReference
    (P.component_probe_absolutelyContinuous p) h _ hs hz

theorem sum_componentChoiDensity_trace_ae (h : H) :
    ∀ᵐ ω ∂P.commonReference h,
      (∑' p, ENNReal.ofReal (P.componentChoiDensity p (h,ω)).trace.re) =
        ENNReal.ofReal (Fintype.card I : ℝ) := by
  let κ (p : ℕ) := (P.componentChoi p).traceKernel
  let μ := P.commonReference
  let d : ℝ := Fintype.card I
  have hd : 0 < d := by
    dsimp only [d]
    exact_mod_cast Fintype.card_pos (α := I)
  letI : IsMarkovKernel μ := P.commonReference_isMarkov
  letI : ∀ p, IsFiniteKernel (κ p) := fun p =>
    CountableReference.component_isFinite κ d P.total_component_trace_mass p
  have hw := CountableReference.ae_sum_componentWeight κ d hd P.total_component_trace_mass h
  filter_upwards [hw, ae_all_iff.mpr (fun p => P.componentChoiDensity_trace_ae_eq p h),
    ae_all_iff.mpr (fun p => Kernel.rnDeriv_ne_top (κ p) μ)] with ω hsum htrace hfinite
  calc
    _ = ∑' p, (κ p).rnDeriv μ h ω := by
      apply tsum_congr
      intro p
      rw [htrace p, ENNReal.ofReal_toReal (hfinite p)]
    _ = _ := hsum

def commonValid (z : H × Ω) : Prop :=
  ((∑' p, ENNReal.ofReal (P.componentChoiDensity p z).trace.re) =
    ENNReal.ofReal (Fintype.card I : ℝ)) ∧
  ∀ p, P.outputTag z = p ∨ P.componentChoiDensity p z = 0

theorem measurableSet_commonValid : MeasurableSet {z | P.commonValid z} := by
  have hm (p : ℕ) : Measurable (fun z : H × Ω =>
      ENNReal.ofReal (P.componentChoiDensity p z).trace.re) := by
    simpa only [Function.comp_apply, traceReCLM_apply] using
      ((traceReCLM (Q := I × Fin p)).continuous.measurable.comp
        (P.measurable_componentChoiDensity p)).ennreal_ofReal
  have hsum := Measurable.ennreal_tsum hm
  simp only [commonValid, Set.setOf_and, Set.setOf_forall, Set.setOf_or]
  exact (measurableSet_eq_fun hsum measurable_const).inter
    (MeasurableSet.iInter fun p =>
      (measurableSet_eq_fun P.measurable_outputTag measurable_const).union
        (measurableSet_eq_fun (P.measurable_componentChoiDensity p) measurable_const))

theorem commonValid_ae (h : H) : ∀ᵐ ω ∂P.commonReference h, P.commonValid (h,ω) := by
  filter_upwards [P.sum_componentChoiDensity_trace_ae h,
    ae_all_iff.mpr (fun p => P.componentChoiDensity_off_tag p h)] with ω hsum hsupport
  refine ⟨hsum, ?_⟩
  intro p
  by_cases hp : P.outputTag (h,ω) = p
  · exact Or.inl hp
  · exact Or.inr (hsupport p hp)

def patchedChoiDensity (p : ℕ) (z : H × Ω) : Matrix (I × Fin p) (I × Fin p) ℂ := by
  classical
  exact if P.commonValid z then P.componentChoiDensity p z else 0

theorem measurable_patchedChoiDensity (p : ℕ) : Measurable (P.patchedChoiDensity p) := by
  classical
  exact Measurable.ite P.measurableSet_commonValid
    (P.measurable_componentChoiDensity p) measurable_const

theorem patchedChoiDensity_posSemidef (p : ℕ) (z : H × Ω) :
    (P.patchedChoiDensity p z).PosSemidef := by
  classical
  letI : ∀ v : I × Fin p → ℂ, IsFiniteKernel ((P.componentChoi p).probe v) :=
    P.component_probe_finite p
  unfold patchedChoiDensity
  split_ifs
  · exact (P.componentChoi p).positiveRelativeDensity_posSemidef P.commonReference z.1 z.2
  · exact Matrix.PosSemidef.zero

theorem patchedChoiDensity_ae_eq (p : ℕ) (h : H) :
    (fun ω => P.patchedChoiDensity p (h,ω)) =ᵐ[P.commonReference h]
      (fun ω => P.componentChoiDensity p (h,ω)) := by
  classical
  filter_upwards [P.commonValid_ae h] with ω hω
  simp only [patchedChoiDensity, if_pos hω]

def patchedComponentDensity (p : ℕ) (h : H) (ω : Ω) :
    Matrix I I ℂ →ₗ[ℂ] Matrix (Fin p) (Fin p) ℂ :=
  fromChoi (P.patchedChoiDensity p (h,ω))

theorem patchedComponentDensity_completelyPositive (p : ℕ) (h : H) (ω : Ω) :
    QuantumProver.ElegantJointMeasurement.CP.CompletelyPositive (P.patchedComponentDensity p h ω) :=
  fromChoi_completelyPositive _ (P.patchedChoiDensity_posSemidef p (h,ω))

theorem patchedComponentDensity_ae_eq (p : ℕ) (h : H) :
    P.patchedComponentDensity p h =ᵐ[P.commonReference h] P.componentDensity p h := by
  filter_upwards [P.patchedChoiDensity_ae_eq p h] with ω hω
  exact congrArg fromChoi hω

theorem patchedComponentDensity_setIntegral (p : ℕ) (h : H) (s : Set Ω)
    (hs : MeasurableSet s) (X : Matrix I I ℂ) :
    (∫ ω in s, P.patchedComponentDensity p h ω X ∂P.commonReference h) =
      (P.component p).map h s X := by
  have he : (fun ω => P.patchedComponentDensity p h ω X) =ᵐ[(P.commonReference h).restrict s]
      (fun ω => P.componentDensity p h ω X) :=
    ae_restrict_of_ae ((P.patchedComponentDensity_ae_eq p h).mono
      (fun ω hω => congrArg (fun Φ => Φ X) hω))
  rw [integral_congr_ae he]
  exact P.componentDensity_setIntegral p h s hs X

end CP.MatrixVaryingCPInstrument
end QuantumProver.ElegantJointMeasurement.ContinuousInstrumentRadonNikodym

namespace QuantumProver.ElegantJointMeasurement.ContinuousInstrumentRadonNikodym
namespace CountableGram
variable {I O : Type*} [Fintype I] [DecidableEq I] [Fintype O] [DecidableEq O]

theorem norm_cp_apply_le_identity_trace
    (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) (hCP : QuantumProver.ElegantJointMeasurement.CP.CompletelyPositive Φ)
    (X : Matrix I I ℂ) : ‖Φ X‖ ≤ ‖X‖ * (Φ 1).trace.re := by
  let Ψ (_ : Unit) := Φ
  let K (q : I × O) := QuantumProver.ElegantJointMeasurement.ContinuousCPInstruments.canonicalKraus Ψ () q
  have hact := QuantumProver.ElegantJointMeasurement.ContinuousCPInstruments.canonicalKraus_matrix_action Ψ
    (fun _ => hCP) () X
  have hterm (q : I × O) : ‖K q * X * (K q)ᴴ‖ ≤
      ‖X‖ * ((K q)ᴴ * K q).trace.re := by
    calc
      _ ≤ ‖K q * X‖ * ‖(K q)ᴴ‖ := Matrix.l2_opNorm_mul _ _
      _ ≤ (‖K q‖ * ‖X‖) * ‖(K q)ᴴ‖ :=
        mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _)
      _ = ‖X‖ * ‖(K q)ᴴ * K q‖ := by
        rw [Matrix.l2_opNorm_conjTranspose, Matrix.l2_opNorm_conjTranspose_mul_self]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (QuantumProver.ElegantJointMeasurement.ContinuousCPInstruments.posSemidef_norm_le_trace _
          (Matrix.posSemidef_conjTranspose_mul_self (K q))) (norm_nonneg _)
  calc
    _ = ‖∑ q, K q * X * (K q)ᴴ‖ := congrArg norm hact
    _ ≤ ∑ q, ‖K q * X * (K q)ᴴ‖ := norm_sum_le _ _
    _ ≤ ∑ q, ‖X‖ * ((K q)ᴴ * K q).trace.re := Finset.sum_le_sum fun q _ => hterm q
    _ = ‖X‖ * (∑ q, (K q)ᴴ * K q).trace.re := by
      rw [← Finset.mul_sum]
      congr 1
      simp only [Matrix.trace_sum, Complex.re_sum]
    _ = ‖X‖ * (Φ 1).trace.re := by
      change ‖X‖ * (QuantumProver.ElegantJointMeasurement.ContinuousCPInstruments.canonicalGram Ψ ()).trace.re = _
      rw [QuantumProver.ElegantJointMeasurement.ContinuousCPInstruments.canonicalGram_trace Ψ (fun _ => hCP)]

end CountableGram

namespace CP.MatrixVaryingCPInstrument
variable {H Ω I : Type*} [MeasurableSpace H] [MeasurableSpace Ω]
  [Fintype I] [DecidableEq I] [Nonempty I]
  [MeasurableSpace.CountableOrCountablyGenerated H Ω]
variable (P : MatrixVaryingCPInstrument (H := H) (Ω := Ω) (I := I))

theorem patchedChoiDensity_trace_le_inputCard (p : ℕ) (z : H × Ω) :
    (P.patchedChoiDensity p z).trace.re ≤ (Fintype.card I : ℝ) := by
  classical
  by_cases hv : P.commonValid z
  · simp only [patchedChoiDensity, if_pos hv]
    apply (ENNReal.ofReal_le_ofReal_iff (Nat.cast_nonneg _)).mp
    calc
      _ ≤ ∑' q, ENNReal.ofReal (P.componentChoiDensity q z).trace.re :=
        ENNReal.le_tsum (f := fun q => ENNReal.ofReal (P.componentChoiDensity q z).trace.re) p
      _ = _ := hv.1
  · simp only [patchedChoiDensity, if_neg hv, Matrix.trace_zero, Complex.zero_re]
    exact Nat.cast_nonneg _

theorem patchedChoiDensity_norm_le_inputCard (p : ℕ) (z : H × Ω) :
    ‖P.patchedChoiDensity p z‖ ≤ (Fintype.card I : ℝ) :=
  (QuantumProver.ElegantJointMeasurement.ContinuousCPInstruments.posSemidef_norm_le_trace _
    (P.patchedChoiDensity_posSemidef p z)).trans
      (P.patchedChoiDensity_trace_le_inputCard p z)

theorem norm_patchedComponentDensity_apply_le (p : ℕ) (h : H) (ω : Ω)
    (X : Matrix I I ℂ) :
    ‖P.patchedComponentDensity p h ω X‖ ≤ ‖X‖ * (Fintype.card I : ℝ) := by
  have he : (P.patchedComponentDensity p h ω 1).trace.re =
      (P.patchedChoiDensity p (h,ω)).trace.re := by
    rw [← QuantumProver.ElegantJointMeasurement.ContinuousCPInstruments.choi_trace]
    simp only [patchedComponentDensity, choi_fromChoi]
  calc
    _ ≤ ‖X‖ * (P.patchedComponentDensity p h ω 1).trace.re :=
      CountableGram.norm_cp_apply_le_identity_trace _
        (P.patchedComponentDensity_completelyPositive p h ω) X
    _ = ‖X‖ * (P.patchedChoiDensity p (h,ω)).trace.re := by rw [he]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (P.patchedChoiDensity_trace_le_inputCard p (h,ω)) (norm_nonneg _)

end CP.MatrixVaryingCPInstrument
end QuantumProver.ElegantJointMeasurement.ContinuousInstrumentRadonNikodym

namespace QuantumProver.ElegantJointMeasurement.ContinuousInstrumentRadonNikodym
namespace CountableReference

def halfParameter : unitInterval := ⟨(1 / 2 : ℝ), by constructor <;> norm_num⟩

theorem halfParameter_ne_zero : halfParameter ≠ 0 := by
  intro he
  have hv := congrArg (fun x : unitInterval => (x : ℝ)) he
  norm_num [halfParameter] at hv

theorem halfParameter_ne_one : halfParameter ≠ 1 := by
  intro he
  have hv := congrArg (fun x : unitInterval => (x : ℝ)) he
  norm_num [halfParameter] at hv

def positiveNatPMF : PMF ℕ :=
  (ProbabilityTheory.geometricMeasure halfParameter).toPMF

theorem positiveNatPMF_pos (n : ℕ) : 0 < positiveNatPMF n := by
  change 0 < ProbabilityTheory.geometricMeasure halfParameter {n}
  rw [ProbabilityTheory.geometricMeasure_singleton halfParameter_ne_zero]
  exact ENNReal.ofReal_pos.mpr
    (ProbabilityTheory.geometricMeasure_pos halfParameter_ne_zero halfParameter_ne_one n)

variable (Q : Type*) [Countable Q] [Nonempty Q]

def fullSupportPMF : PMF Q :=
  positiveNatPMF.map (Classical.choose (exists_surjective_nat Q))

theorem fullSupportPMF_pos (q : Q) : 0 < fullSupportPMF Q q := by
  apply ((fullSupportPMF Q).apply_pos_iff q).mpr
  rw [fullSupportPMF, PMF.mem_support_map_iff]
  obtain ⟨n, hn⟩ := Classical.choose_spec (exists_surjective_nat Q) q
  exact ⟨n, (positiveNatPMF.apply_pos_iff n).mp (positiveNatPMF_pos n), hn⟩

theorem fullSupportPMF_toReal_pos (q : Q) :
    0 < (fullSupportPMF Q q).toReal :=
  ENNReal.toReal_pos_iff.mpr
    ⟨fullSupportPMF_pos Q q, (fullSupportPMF Q).apply_lt_top q⟩

end CountableReference

namespace CountableProbabilityRefinement
variable {Q E : Type*} [Countable Q] [MeasurableSpace Q]
  [MeasurableSingletonClass Q] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E]
variable (π : PMF Q) (hπ : ∀ q, 0 < π q)

def inverseMass (q : Q) : ℝ := (π q).toReal⁻¹

include hπ

theorem mass_toReal_pos (q : Q) : 0 < (π q).toReal :=
  ENNReal.toReal_pos_iff.mpr ⟨hπ q, π.apply_lt_top q⟩

theorem inverseMass_pos (q : Q) : 0 < inverseMass π q :=
  inv_pos.mpr (mass_toReal_pos π hπ q)

theorem mass_cancel (q : Q) : (π q).toReal * inverseMass π q = 1 :=
  mul_inv_cancel₀ (mass_toReal_pos π hπ q).ne'

omit hπ in theorem toMeasure_eq_sum_dirac :
    π.toMeasure = Measure.sum (fun q => π q • Measure.dirac q) := by
  calc
    _ = Measure.sum (fun q => π.toMeasure {q} • Measure.dirac q) :=
      (Measure.sum_smul_dirac π.toMeasure).symm
    _ = _ := by
      congr 1
      funext q
      rw [π.toMeasure_apply_singleton q (measurableSet_singleton q)]

theorem mass_smul_inverseMass (q : Q) (x : E) :
    (π q).toReal • (inverseMass π q • x) = x := by
  rw [smul_smul, mass_cancel π hπ q, one_smul]

theorem integrable_inverseMass_smul (f : Q → E)
    (hf : Summable (fun q => ‖f q‖)) :
    Integrable (fun q => inverseMass π q • f q) π.toMeasure := by
  rw [toMeasure_eq_sum_dirac π]
  apply integrable_sum_dirac (fun q => π.apply_ne_top q)
  convert hf using 1
  funext q
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inverseMass_pos π hπ q),
    ← mul_assoc, mass_cancel π hπ q, one_mul]

theorem integral_inverseMass_smul (f : Q → E)
    (hf : Summable (fun q => ‖f q‖)) :
    (∫ q, inverseMass π q • f q ∂π.toMeasure) = ∑' q, f q := by
  rw [PMF.integral_eq_tsum π _ (integrable_inverseMass_smul π hπ f hf)]
  exact tsum_congr fun q => mass_smul_inverseMass π hπ q (f q)

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [SFinite μ]

theorem integrable_prod_inverseMass_smul (f : Ω × Q → E)
    (hfm : StronglyMeasurable f) (hf : ∀ q, Integrable (fun ω => f (ω,q)) μ)
    (hs : Summable (fun q => ∫ ω, ‖f (ω,q)‖ ∂μ)) :
    Integrable (fun z => inverseMass π z.2 • f z) (μ.prod π.toMeasure) := by
  have hw : StronglyMeasurable (fun z : Ω × Q => inverseMass π z.2) :=
    ((Measurable.of_discrete : Measurable (inverseMass π)).comp
      measurable_snd).stronglyMeasurable
  apply (integrable_prod_iff' (hw.smul hfm).aestronglyMeasurable).mpr
  constructor
  · exact ae_of_all _ fun q => (hf q).smul (inverseMass π q)
  · have he (q : Q) : (∫ ω, ‖inverseMass π q • f (ω,q)‖ ∂μ) =
        inverseMass π q • (∫ ω, ‖f (ω,q)‖ ∂μ) := by
      simp_rw [norm_smul, Real.norm_eq_abs,
        abs_of_pos (inverseMass_pos π hπ q)]
      rw [integral_const_mul]
      rfl
    change Integrable (fun q => ∫ ω, ‖inverseMass π q • f (ω,q)‖ ∂μ) π.toMeasure
    simp_rw [he]
    exact integrable_inverseMass_smul π hπ _ hs.norm

theorem integral_prod_inverseMass_smul (f : Ω × Q → E)
    (hfm : StronglyMeasurable f) (hf : ∀ q, Integrable (fun ω => f (ω,q)) μ)
    (hs : Summable (fun q => ∫ ω, ‖f (ω,q)‖ ∂μ)) :
    (∫ z, inverseMass π z.2 • f z ∂μ.prod π.toMeasure) =
      ∑' q, ∫ ω, f (ω,q) ∂μ := by
  have hm : Summable (fun q => ‖∫ ω, f (ω,q) ∂μ‖) :=
    Summable.of_nonneg_of_le (fun q => norm_nonneg _)
      (fun q => norm_integral_le_integral_norm _) hs
  rw [integral_prod_symm _ (integrable_prod_inverseMass_smul π hπ μ f hfm hf hs)]
  simp_rw [integral_smul]
  exact integral_inverseMass_smul π hπ _ hm

end CountableProbabilityRefinement

namespace CP.MatrixVaryingCPInstrument
variable {H Ω I : Type*} [MeasurableSpace H] [MeasurableSpace Ω]
  [Fintype I] [DecidableEq I] [Nonempty I]
  [MeasurableSpace I] [MeasurableSingletonClass I]
  [MeasurableSpace.CountableOrCountablyGenerated H Ω]
variable (P : MatrixVaryingCPInstrument (H := H) (Ω := Ω) (I := I))

instance hiddenColumn_countable : Countable (HiddenColumn I) := by
  unfold HiddenColumn
  infer_instance

instance hiddenColumn_nonempty : Nonempty (HiddenColumn I) :=
  ⟨⟨1, (Classical.choice (inferInstance : Nonempty I), 0)⟩⟩

def hiddenPMF : PMF (HiddenColumn I) :=
  CountableReference.fullSupportPMF (HiddenColumn I)

theorem hiddenPMF_pos (q : HiddenColumn I) : 0 < hiddenPMF (I := I) q :=
  CountableReference.fullSupportPMF_pos _ q

theorem hiddenColumn_output_pos (q : HiddenColumn I) : 0 < q.1 :=
  lt_of_le_of_lt (Nat.zero_le q.2.2.val) q.2.2.isLt

def countableRefinedKernel : Kernel H (Ω × HiddenColumn I) :=
  P.commonReference ×ₖ Kernel.const H (hiddenPMF (I := I)).toMeasure

instance countableRefinedKernel_isMarkov : IsMarkovKernel P.countableRefinedKernel := by
  unfold countableRefinedKernel
  infer_instance

theorem countableRefinedKernel_apply (h : H) :
    P.countableRefinedKernel h = (P.commonReference h).prod
      (hiddenPMF (I := I)).toMeasure := by
  rw [countableRefinedKernel, Kernel.prod_apply, Kernel.const_apply]

end CP.MatrixVaryingCPInstrument
end QuantumProver.ElegantJointMeasurement.ContinuousInstrumentRadonNikodym

namespace QuantumProver.ElegantJointMeasurement.ContinuousInstrumentRadonNikodym
namespace CP.MatrixVaryingCPInstrument
variable {H Ω I : Type*} [MeasurableSpace H] [MeasurableSpace Ω]
  [Fintype I] [DecidableEq I] [Nonempty I]
  [MeasurableSpace I] [MeasurableSingletonClass I]
  [MeasurableSpace.CountableOrCountablyGenerated H Ω]
variable (P : MatrixVaryingCPInstrument (H := H) (Ω := Ω) (I := I))

theorem hiddenGram_posSemidef (z : H × Ω) (q : HiddenColumn I) :
    (P.hiddenGram z q).PosSemidef :=
  Matrix.posSemidef_conjTranspose_mul_self _

theorem hiddenGram_le_componentGram (z : H × Ω) (q : HiddenColumn I) :
    P.hiddenGram z q ≤ P.componentGram q.1 z.1 z.2 := by
  change (QuantumProver.ElegantJointMeasurement.ContinuousCPInstruments.canonicalKraus (P.componentDensity q.1 z.1) z.2 q.2)ᴴ *
    QuantumProver.ElegantJointMeasurement.ContinuousCPInstruments.canonicalKraus (P.componentDensity q.1 z.1) z.2 q.2 ≤
    ∑ r : I × Fin q.1,
    (QuantumProver.ElegantJointMeasurement.ContinuousCPInstruments.canonicalKraus (P.componentDensity q.1 z.1) z.2 r)ᴴ *
      QuantumProver.ElegantJointMeasurement.ContinuousCPInstruments.canonicalKraus (P.componentDensity q.1 z.1) z.2 r
  exact Finset.single_le_sum (f := fun r : I × Fin q.1 =>
    (QuantumProver.ElegantJointMeasurement.ContinuousCPInstruments.canonicalKraus (P.componentDensity q.1 z.1) z.2 r)ᴴ *
      QuantumProver.ElegantJointMeasurement.ContinuousCPInstruments.canonicalKraus (P.componentDensity q.1 z.1) z.2 r) (fun r _ =>
    (Matrix.posSemidef_conjTranspose_mul_self _).nonneg) (Finset.mem_univ q.2)

theorem hiddenGram_integrable (h : H) (q : HiddenColumn I) :
    Integrable (fun ω => P.hiddenGram (h,ω) q) (P.commonReference h) := by
  have hm : Measurable (fun ω => P.hiddenGram (h,ω) q) :=
    P.measurable_hiddenGram.comp
      ((measurable_const.prodMk measurable_id).prodMk measurable_const)
  apply (P.componentGram_integrable q.1 h).norm.mono'
    hm.stronglyMeasurable.aestronglyMeasurable
  exact ae_of_all _ fun ω => CStarAlgebra.norm_le_norm_of_le_of_nonneg
    (P.hiddenGram_le_componentGram (h,ω) q) (P.hiddenGram_posSemidef (h,ω) q).nonneg

theorem sum_hiddenGram_eq_componentGram (p : ℕ) (z : H × Ω) :
    (∑ q : I × Fin p, P.hiddenGram z ⟨p,q⟩) = P.componentGram p z.1 z.2 := rfl

theorem sum_integral_hiddenGram_eq_integral_componentGram (p : ℕ) (h : H) :
    (∑ q : I × Fin p, ∫ ω, P.hiddenGram (h,ω) ⟨p,q⟩ ∂P.commonReference h) =
      ∫ ω, P.componentGram p h ω ∂P.commonReference h := by
  rw [← integral_finset_sum Finset.univ (fun q _ => P.hiddenGram_integrable h ⟨p,q⟩)]
  rfl

theorem integral_norm_hiddenGram_le_trace_mean (h : H) (q : HiddenColumn I) :
    (∫ ω, ‖P.hiddenGram (h,ω) q‖ ∂P.commonReference h) ≤
      (∫ ω, P.hiddenGram (h,ω) q ∂P.commonReference h).trace.re := by
  have hg := P.hiddenGram_integrable h q
  have ht : Integrable (fun ω => (P.hiddenGram (h,ω) q).trace.re)
      (P.commonReference h) := by
    simpa only [traceReCLM_apply] using (traceReCLM (Q := I)).integrable_comp hg
  have he : (∫ ω, (P.hiddenGram (h,ω) q).trace.re ∂P.commonReference h) =
      (∫ ω, P.hiddenGram (h,ω) q ∂P.commonReference h).trace.re := by
    simpa only [traceReCLM_apply] using (traceReCLM (Q := I)).integral_comp_comm hg
  calc
    _ ≤ ∫ ω, (P.hiddenGram (h,ω) q).trace.re ∂P.commonReference h :=
      integral_mono hg.norm ht fun ω =>
        QuantumProver.ElegantJointMeasurement.ContinuousCPInstruments.posSemidef_norm_le_trace _
          (P.hiddenGram_posSemidef (h,ω) q)
    _ = _ := he

theorem sum_integral_norm_hiddenGram_le_componentTrace (p : ℕ) (h : H) :
    (∑ q : I × Fin p, ∫ ω, ‖P.hiddenGram (h,ω) ⟨p,q⟩‖ ∂P.commonReference h) ≤
      (∫ ω, P.componentGram p h ω ∂P.commonReference h).trace.re := by
  calc
    _ ≤ ∑ q : I × Fin p,
        (∫ ω, P.hiddenGram (h,ω) ⟨p,q⟩ ∂P.commonReference h).trace.re :=
      Finset.sum_le_sum fun q _ => P.integral_norm_hiddenGram_le_trace_mean h ⟨p,q⟩
    _ = _ := by
      rw [← Complex.re_sum, ← Matrix.trace_sum,
        P.sum_integral_hiddenGram_eq_integral_componentGram p h]

theorem summable_integral_norm_hiddenGram (h : H) :
    Summable (fun q : HiddenColumn I =>
      ∫ ω, ‖P.hiddenGram (h,ω) q‖ ∂P.commonReference h) := by
  have ht : Summable (fun p =>
      (∫ ω, P.componentGram p h ω ∂P.commonReference h).trace.re) := by
    simpa only [traceReCLM_apply] using
      ((traceReCLM (Q := I)).hasSum (P.hasSum_integral_componentGram h)).summable
  apply (summable_sigma_of_nonneg (fun q => integral_nonneg (fun ω => norm_nonneg _))).mpr
  constructor
  · intro p
    exact (hasSum_fintype _).summable
  · simp only [tsum_fintype]
    exact Summable.of_nonneg_of_le
      (fun p => Finset.sum_nonneg fun q _ => integral_nonneg fun ω => norm_nonneg _)
      (fun p => P.sum_integral_norm_hiddenGram_le_componentTrace p h) ht

theorem summable_integral_hiddenGram (h : H) :
    Summable (fun q : HiddenColumn I =>
      ∫ ω, P.hiddenGram (h,ω) q ∂P.commonReference h) :=
  (P.summable_integral_norm_hiddenGram h).of_norm_bounded
    (fun q => norm_integral_le_integral_norm _)

theorem tsum_integral_hiddenGram (h : H) :
    (∑' q : HiddenColumn I, ∫ ω, P.hiddenGram (h,ω) q ∂P.commonReference h) =
      (1 : Matrix I I ℂ) := by
  rw [(P.summable_integral_hiddenGram h).tsum_sigma]
  simp only [tsum_fintype]
  simp_rw [P.sum_integral_hiddenGram_eq_integral_componentGram]
  exact (P.hasSum_integral_componentGram h).tsum_eq

def countableRefinedGram (z : H × (Ω × HiddenColumn I)) : Matrix I I ℂ :=
  CountableProbabilityRefinement.inverseMass (hiddenPMF (I := I)) z.2.2 •
    P.hiddenGram (z.1,z.2.1) z.2.2

theorem hiddenGram_stronglyMeasurable (h : H) :
    StronglyMeasurable (fun z : Ω × HiddenColumn I => P.hiddenGram (h,z.1) z.2) :=
  (P.measurable_hiddenGram.comp
    ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)).stronglyMeasurable

theorem countableRefinedGram_integrable (h : H) :
    Integrable (fun r => P.countableRefinedGram (h,r)) (P.countableRefinedKernel h) := by
  rw [P.countableRefinedKernel_apply]
  exact CountableProbabilityRefinement.integrable_prod_inverseMass_smul
    (hiddenPMF (I := I)) hiddenPMF_pos (P.commonReference h)
    (fun z => P.hiddenGram (h,z.1) z.2) (P.hiddenGram_stronglyMeasurable h)
    (fun q => P.hiddenGram_integrable h q) (P.summable_integral_norm_hiddenGram h)

theorem integral_countableRefinedGram (h : H) :
    (∫ r, P.countableRefinedGram (h,r) ∂P.countableRefinedKernel h) =
      (1 : Matrix I I ℂ) := by
  rw [P.countableRefinedKernel_apply]
  exact (CountableProbabilityRefinement.integral_prod_inverseMass_smul
    (hiddenPMF (I := I)) hiddenPMF_pos (P.commonReference h)
    (fun z => P.hiddenGram (h,z.1) z.2) (P.hiddenGram_stronglyMeasurable h)
    (fun q => P.hiddenGram_integrable h q) (P.summable_integral_norm_hiddenGram h)).trans
      (P.tsum_integral_hiddenGram h)

end CP.MatrixVaryingCPInstrument
end QuantumProver.ElegantJointMeasurement.ContinuousInstrumentRadonNikodym

namespace QuantumProver.ElegantJointMeasurement.ContinuousInstrumentRadonNikodym
namespace CP.MatrixVaryingCPInstrument
variable {H Ω I : Type*} [MeasurableSpace H] [MeasurableSpace Ω]
  [Fintype I] [DecidableEq I] [Nonempty I]
  [MeasurableSpace I] [MeasurableSingletonClass I]
  [MeasurableSpace.CountableOrCountablyGenerated H Ω]
variable (P : MatrixVaryingCPInstrument (H := H) (Ω := Ω) (I := I))

def coarseTaggedProjection (r : Ω × HiddenColumn I) : Ω × ℕ := (r.1,r.2.1)

theorem measurable_coarseTaggedProjection :
    Measurable (coarseTaggedProjection (Ω := Ω) (I := I)) := by
  exact measurable_fst.prodMk
    ((Measurable.of_discrete : Measurable (fun q : HiddenColumn I => q.1)).comp
      measurable_snd)

theorem coarseTaggedProjection_dimension (r : Ω × HiddenColumn I) :
    (coarseTaggedProjection r).2 = r.2.1 := rfl

theorem zero_component_action (h : H) (s : Set Ω) (X : Matrix I I ℂ) :
    (P.component 0).map h s X = 0 := by
  rw [P.zero_component_map]
  rfl

theorem zero_component_choi (h : H) (s : Set Ω) :
    (P.componentChoi 0).effect h s = 0 := by
  ext a b
  exact isEmptyElim a.2

theorem zero_componentDensity (h : H) (ω : Ω) : P.componentDensity 0 h ω = 0 := by
  apply LinearMap.ext
  intro X
  ext b c
  exact isEmptyElim b

theorem commonValid_outputTag_ne_zero (z : H × Ω) (hv : P.commonValid z) :
    P.outputTag z ≠ 0 := by
  intro hzero
  have hz (p : ℕ) : P.componentChoiDensity p z = 0 := by
    by_cases hp : p = 0
    · subst p
      ext a b
      exact isEmptyElim a.2
    · exact (hv.2 p).resolve_left (fun he => hp (he.symm.trans hzero))
  have hsum : (∑' p, ENNReal.ofReal (P.componentChoiDensity p z).trace.re) = 0 := by
    simp_rw [hz, Matrix.trace_zero, Complex.zero_re, ENNReal.ofReal_zero]
    exact tsum_zero
  have hd : 0 < ENNReal.ofReal (Fintype.card I : ℝ) :=
    ENNReal.ofReal_pos.mpr (by exact_mod_cast Fintype.card_pos (α := I))
  exact hd.ne' (hv.1.symm.trans hsum)

theorem commonReference_zero_output_measure (h : H) :
    P.commonReference h {ω | P.outputTag (h,ω) = 0} = 0 := by
  apply measure_eq_zero_iff_ae_notMem.mpr
  filter_upwards [P.commonValid_ae h] with ω hω
  exact P.commonValid_outputTag_ne_zero (h,ω) hω

theorem patchedChoiDensity_zero_of_off_tag (p : ℕ) (z : H × Ω)
    (hp : P.outputTag z ≠ p) : P.patchedChoiDensity p z = 0 := by
  classical
  by_cases hv : P.commonValid z
  · simp only [patchedChoiDensity, if_pos hv]
    exact (hv.2 p).resolve_left hp
  · simp only [patchedChoiDensity, if_neg hv]

theorem patchedComponentDensity_zero_of_off_tag (p : ℕ) (z : H × Ω)
    (hp : P.outputTag z ≠ p) : P.patchedComponentDensity p z.1 z.2 = 0 := by
  change fromChoi (P.patchedChoiDensity p z) = 0
  rw [P.patchedChoiDensity_zero_of_off_tag p z hp]
  apply LinearMap.ext
  intro X
  ext b c
  change (∑ i : I, ∑ j : I, X i j * (0 : ℂ)) = 0
  simp

end CP.MatrixVaryingCPInstrument
end QuantumProver.ElegantJointMeasurement.ContinuousInstrumentRadonNikodym

namespace QuantumProver.ElegantJointMeasurement.ContinuousInstrumentRadonNikodym
namespace CP.MatrixVaryingCPInstrument
variable {H Ω : Type*} [MeasurableSpace H] [MeasurableSpace Ω]
  [MeasurableSpace.CountableOrCountablyGenerated H Ω]
variable {m : ℕ} [NeZero m]
variable (P : MatrixVaryingCPInstrument (H := H) (Ω := Ω) (I := Fin m))

theorem patchedComponentDensity_joint_coordinate_measurable (p : ℕ)
    (i j : Fin m) (b c : Fin p) :
    Measurable (fun z : H × Ω =>
      P.patchedComponentDensity p z.1 z.2 (Matrix.single i j 1) b c) := by
  simp only [patchedComponentDensity, fromChoi_matrix_unit]
  exact (measurable_pi_iff.mp (measurable_pi_iff.mp
    (P.measurable_patchedChoiDensity p) (i,b))) (j,c)

def branchKraus (z : H × Ω) (q : HiddenColumn (Fin m)) : Matrix (Fin q.1) (Fin m) ℂ :=
  QuantumProver.ElegantJointMeasurement.CP.krausOperator (P.patchedComponentDensity q.1 z.1 z.2) q.2

def branchSquare (z : H × Ω) (q : HiddenColumn (Fin m)) : Matrix (Fin m) (Fin m) ℂ :=
  QuantumProver.ElegantJointMeasurement.CP.positiveInputKraus (P.branchKraus z q)

def branchRecovery (z : H × Ω) (q : HiddenColumn (Fin m)) : QuantumProver.ElegantJointMeasurement.CP.LocalRecovery m q.1 :=
  QuantumProver.ElegantJointMeasurement.CP.LocalRecovery.rectangular (hiddenColumn_output_pos q) (P.branchKraus z q)

theorem measurable_branchKraus (q : HiddenColumn (Fin m)) :
    Measurable (fun z : H × Ω => P.branchKraus z q) :=
  QuantumProver.ElegantJointMeasurement.ContinuousCPInstruments.measurable_canonicalKraus _
    (P.patchedComponentDensity_joint_coordinate_measurable q.1) q.2

theorem measurable_branchSquare (q : HiddenColumn (Fin m)) :
    Measurable (fun z : H × Ω => P.branchSquare z q) :=
  QuantumProver.ElegantJointMeasurement.CP.measurable_positiveInputKraus.comp (P.measurable_branchKraus q)

theorem branchSquare_posSemidef (z : H × Ω) (q : HiddenColumn (Fin m)) :
    (P.branchSquare z q).PosSemidef := QuantumProver.ElegantJointMeasurement.CP.positiveInputKraus_posSemidef _

theorem branchRecovery_matrixUnitMeasurable (q : HiddenColumn (Fin m)) :
    QuantumProver.ElegantJointMeasurement.CP.MatrixUnitMeasurable (fun z : H × Ω => (P.branchRecovery z q).map) :=
  QuantumProver.ElegantJointMeasurement.CP.pendingRecoveryField_matrixUnitMeasurable (hiddenColumn_output_pos q)
    (fun z => P.branchKraus z q) (P.measurable_branchKraus q)

theorem branchRecovery_square_action (z : H × Ω) (q : HiddenColumn (Fin m))
    (X : Matrix (Fin m) (Fin m) ℂ) :
    (P.branchRecovery z q).map (P.branchSquare z q * X * (P.branchSquare z q)ᴴ) =
      P.branchKraus z q * X * (P.branchKraus z q)ᴴ :=
  QuantumProver.ElegantJointMeasurement.CP.rectangularRecovery_apply (hiddenColumn_output_pos q) _ X

def countableRefinedSquare (z : H × (Ω × HiddenColumn (Fin m))) :
    Matrix (Fin m) (Fin m) ℂ :=
  QuantumProver.ElegantJointMeasurement.ContinuousInstrumentQuadrature.weightedKraus
    (CountableProbabilityRefinement.inverseMass (hiddenPMF (I := Fin m)) z.2.2)
    (P.branchSquare (z.1,z.2.1) z.2.2)

def countableRefinedRecovery (z : H × (Ω × HiddenColumn (Fin m))) :
    QuantumProver.ElegantJointMeasurement.CP.LocalRecovery m z.2.2.1 := P.branchRecovery (z.1,z.2.1) z.2.2

attribute [local irreducible] hiddenPMF CountableReference.fullSupportPMF

theorem measurable_countableRefinedSquare : Measurable P.countableRefinedSquare := by
  have hglue (w : HiddenColumn (Fin m) → ℝ) :
      Measurable (fun z : (H × Ω) × HiddenColumn (Fin m) =>
        QuantumProver.ElegantJointMeasurement.ContinuousInstrumentQuadrature.weightedKraus (w z.2)
          (P.branchSquare z.1 z.2)) := by
    apply measurable_from_prod_countable_left
    intro q
    apply Measurable.of_eval
    intro i
    apply Measurable.of_eval
    intro j
    change Measurable (fun z : H × Ω => Real.sqrt (w q) • P.branchSquare z q i j)
    exact ((measurable_pi_apply j).comp
      ((measurable_pi_apply i).comp (P.measurable_branchSquare q))).const_smul (Real.sqrt (w q))
  trace "C17 abstract weightedKraus gluing complete"
  have ha : Measurable (fun z : H × (Ω × HiddenColumn (Fin m)) =>
      ((z.1,z.2.1),z.2.2)) :=
    (measurable_fst.prodMk (measurable_fst.comp measurable_snd)).prodMk
      (measurable_snd.comp measurable_snd)
  trace "C17 reassociation measurable"
  have hf := (hglue (fun q =>
    CountableProbabilityRefinement.inverseMass (hiddenPMF (I := Fin m)) q)).comp ha
  trace "C17 actual inverse mass instantiated"
  change Measurable (fun z : H × (Ω × HiddenColumn (Fin m)) => P.countableRefinedSquare z)
  simpa only [countableRefinedSquare, Function.comp_def] using hf

theorem countableRefinedSquare_posSemidef (z : H × (Ω × HiddenColumn (Fin m))) :
    (P.countableRefinedSquare z).PosSemidef :=
  (P.branchSquare_posSemidef _ _).smul (α := ℝ) (Real.sqrt_nonneg _)

theorem countableRefinedSquare_gram (z : H × (Ω × HiddenColumn (Fin m))) :
    (P.countableRefinedSquare z)ᴴ * P.countableRefinedSquare z =
      CountableProbabilityRefinement.inverseMass (hiddenPMF (I := Fin m)) z.2.2 •
        ((P.branchKraus (z.1,z.2.1) z.2.2)ᴴ * P.branchKraus (z.1,z.2.1) z.2.2) := by
  rw [countableRefinedSquare, QuantumProver.ElegantJointMeasurement.ContinuousInstrumentQuadrature.weightedKraus_gram _ _
    (CountableProbabilityRefinement.inverseMass_pos _ hiddenPMF_pos _).le]
  exact congrArg (_ • ·) (QuantumProver.ElegantJointMeasurement.CP.positiveInputKraus_gram _)

theorem countableRefinedRecovery_square_action (z : H × (Ω × HiddenColumn (Fin m)))
    (X : Matrix (Fin m) (Fin m) ℂ) :
    (P.countableRefinedRecovery z).map
      (P.countableRefinedSquare z * X * (P.countableRefinedSquare z)ᴴ) =
      CountableProbabilityRefinement.inverseMass (hiddenPMF (I := Fin m)) z.2.2 •
        (P.branchKraus (z.1,z.2.1) z.2.2 * X *
          (P.branchKraus (z.1,z.2.1) z.2.2)ᴴ) := by
  have hs : P.countableRefinedSquare z * X * (P.countableRefinedSquare z)ᴴ =
      CountableProbabilityRefinement.inverseMass (hiddenPMF (I := Fin m)) z.2.2 •
        (P.branchSquare (z.1,z.2.1) z.2.2 * X *
          (P.branchSquare (z.1,z.2.1) z.2.2)ᴴ) := by
    simp only [countableRefinedSquare, QuantumProver.ElegantJointMeasurement.ContinuousInstrumentQuadrature.weightedKraus,
      Matrix.conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul,
      smul_smul, Real.mul_self_sqrt
        (CountableProbabilityRefinement.inverseMass_pos _ hiddenPMF_pos _).le]
  rw [hs, LinearMap.map_smul_of_tower]
  exact congrArg (_ • ·) (P.branchRecovery_square_action _ _ X)

theorem branchKraus_eq_matrix_of_commonValid (z : H × Ω) (q : HiddenColumn (Fin m))
    (hv : P.commonValid z) : P.branchKraus z q =
      QuantumProver.ElegantJointMeasurement.ContinuousCPInstruments.canonicalKraus (P.componentDensity q.1 z.1) z.2 q.2 := by
  simp only [branchKraus, patchedComponentDensity, patchedChoiDensity, if_pos hv,
    componentChoiDensity, componentDensity, QuantumProver.ElegantJointMeasurement.ContinuousCPInstruments.canonicalKraus]

theorem countableRefinedSquare_gram_ae (h : H) :
    (fun r => (P.countableRefinedSquare (h,r))ᴴ * P.countableRefinedSquare (h,r))
      =ᵐ[P.countableRefinedKernel h] (fun r => P.countableRefinedGram (h,r)) := by
  rw [P.countableRefinedKernel_apply]
  have hv : ∀ᵐ r ∂(P.commonReference h).prod (hiddenPMF (I := Fin m)).toMeasure,
      P.commonValid (h,r.1) := Measure.quasiMeasurePreserving_fst.ae (P.commonValid_ae h)
  filter_upwards [hv] with r hr
  rw [P.countableRefinedSquare_gram, P.branchKraus_eq_matrix_of_commonValid _ _ hr]
  rfl

theorem countableRefinedSquare_gram_integrable (h : H) :
    Integrable (fun r => (P.countableRefinedSquare (h,r))ᴴ *
      P.countableRefinedSquare (h,r)) (P.countableRefinedKernel h) :=
  (P.countableRefinedGram_integrable h).congr (P.countableRefinedSquare_gram_ae h).symm

theorem integral_countableRefinedSquare_gram (h : H) :
    (∫ r, (P.countableRefinedSquare (h,r))ᴴ * P.countableRefinedSquare (h,r)
      ∂P.countableRefinedKernel h) = 1 := by
  rw [integral_congr_ae (P.countableRefinedSquare_gram_ae h)]
  exact P.integral_countableRefinedGram h

end CP.MatrixVaryingCPInstrument
end QuantumProver.ElegantJointMeasurement.ContinuousInstrumentRadonNikodym

namespace QuantumProver.ElegantJointMeasurement.ContinuousInstrumentRadonNikodym
namespace CP.MatrixVaryingCPInstrument
variable {H Ω : Type*} [MeasurableSpace H] [MeasurableSpace Ω]
  [MeasurableSpace.CountableOrCountablyGenerated H Ω]
variable {m : ℕ} [NeZero m]
variable (P : MatrixVaryingCPInstrument (H := H) (Ω := Ω) (I := Fin m))

theorem patchedComponentDensity_integrable (p : ℕ) (h : H)
    (X : Matrix (Fin m) (Fin m) ℂ) :
    Integrable (fun ω => P.patchedComponentDensity p h ω X) (P.commonReference h) := by
  apply (P.componentDensity_integrable p h X).congr
  filter_upwards [P.patchedComponentDensity_ae_eq p h] with ω hω
  exact congrArg (fun Φ => Φ X) hω.symm

def countableRecoveredComponent (p : ℕ) (z : H × Ω)
    (X : Matrix (Fin m) (Fin m) ℂ) : Matrix (Fin p) (Fin p) ℂ :=
  ∑ q : Fin m × Fin p, (hiddenPMF (I := Fin m) ⟨p,q⟩).toReal •
    (P.branchRecovery z ⟨p,q⟩).map
      (P.countableRefinedSquare (z.1,(z.2,⟨p,q⟩)) * X *
        (P.countableRefinedSquare (z.1,(z.2,⟨p,q⟩)))ᴴ)

theorem countableRecoveredComponent_eq (p : ℕ) (z : H × Ω)
    (X : Matrix (Fin m) (Fin m) ℂ) :
    P.countableRecoveredComponent p z X = P.patchedComponentDensity p z.1 z.2 X := by
  have he (q : Fin m × Fin p) :
      (hiddenPMF (I := Fin m) ⟨p,q⟩).toReal •
        (P.branchRecovery z ⟨p,q⟩).map
          (P.countableRefinedSquare (z.1,(z.2,⟨p,q⟩)) * X *
            (P.countableRefinedSquare (z.1,(z.2,⟨p,q⟩)))ᴴ) =
        P.branchKraus z ⟨p,q⟩ * X * (P.branchKraus z ⟨p,q⟩)ᴴ := by
    change (hiddenPMF (I := Fin m) ⟨p,q⟩).toReal •
      (P.countableRefinedRecovery (z.1,(z.2,⟨p,q⟩))).map
        (P.countableRefinedSquare (z.1,(z.2,⟨p,q⟩)) * X *
          (P.countableRefinedSquare (z.1,(z.2,⟨p,q⟩)))ᴴ) = _
    rw [P.countableRefinedRecovery_square_action,
      CountableProbabilityRefinement.mass_smul_inverseMass _ hiddenPMF_pos]
  calc
    _ = ∑ q : Fin m × Fin p, P.branchKraus z ⟨p,q⟩ * X *
        (P.branchKraus z ⟨p,q⟩)ᴴ := Finset.sum_congr rfl fun q _ => he q
    _ = _ := (QuantumProver.ElegantJointMeasurement.ContinuousCPInstruments.canonicalKraus_matrix_action
      (fun z : H × Ω => P.patchedComponentDensity p z.1 z.2)
      (fun z => P.patchedComponentDensity_completelyPositive p z.1 z.2) z X).symm

theorem countableRecoveredComponent_integrable (p : ℕ) (h : H)
    (X : Matrix (Fin m) (Fin m) ℂ) :
    Integrable (fun ω => P.countableRecoveredComponent p (h,ω) X) (P.commonReference h) := by
  simp_rw [P.countableRecoveredComponent_eq]
  exact P.patchedComponentDensity_integrable p h X

theorem countableRecoveredComponent_setIntegral (p : ℕ) (h : H) (s : Set Ω)
    (hs : MeasurableSet s) (X : Matrix (Fin m) (Fin m) ℂ) :
    (∫ ω in s, P.countableRecoveredComponent p (h,ω) X ∂P.commonReference h) =
      (P.component p).map h s X := by
  simp_rw [P.countableRecoveredComponent_eq]
  exact P.patchedComponentDensity_setIntegral p h s hs X

theorem countableRecoveredComponent_zero_of_off_tag (p : ℕ) (z : H × Ω)
    (hp : P.outputTag z ≠ p) (X : Matrix (Fin m) (Fin m) ℂ) :
    P.countableRecoveredComponent p z X = 0 := by
  rw [P.countableRecoveredComponent_eq, P.patchedComponentDensity_zero_of_off_tag p z hp]
  rfl

theorem countableRecoveredComponent_zeroOutput (z : H × Ω)
    (X : Matrix (Fin m) (Fin m) ℂ) : P.countableRecoveredComponent 0 z X = 0 := by
  ext b c
  exact isEmptyElim b

end CP.MatrixVaryingCPInstrument
end QuantumProver.ElegantJointMeasurement.ContinuousInstrumentRadonNikodym

namespace QuantumProver.ElegantJointMeasurement.ContinuousInstrumentRadonNikodym.CP.MatrixVaryingCPInstrument
variable {H Ω : Type*} [MeasurableSpace H] [MeasurableSpace Ω]
  [MeasurableSpace.CountableOrCountablyGenerated H Ω]
variable {m : ℕ} [NeZero m]
variable (P : MatrixVaryingCPInstrument (H := H) (Ω := Ω) (I := Fin m))

theorem patchedComponentDensity_zero_of_not_commonValid (p : ℕ) (z : H × Ω)
    (hv : ¬ P.commonValid z) : P.patchedComponentDensity p z.1 z.2 = 0 := by
  change fromChoi (P.patchedChoiDensity p z) = 0
  simp only [patchedChoiDensity, if_neg hv]
  apply LinearMap.ext
  intro X
  ext b c
  change (∑ i : Fin m, ∑ j : Fin m, X i j * (0 : ℂ)) = 0
  simp

theorem branchKraus_zero_of_component_zero (z : H × Ω) (q : HiddenColumn (Fin m))
    (hz : P.patchedComponentDensity q.1 z.1 z.2 = 0) : P.branchKraus z q = 0 := by
  unfold branchKraus
  rw [hz]
  have hc : QuantumProver.ElegantJointMeasurement.CP.choi
      (0 : Matrix (Fin m) (Fin m) ℂ →ₗ[ℂ] Matrix (Fin q.1) (Fin q.1) ℂ) = 0 := by
    rfl
  ext b i
  simp only [QuantumProver.ElegantJointMeasurement.CP.krausOperator, QuantumProver.ElegantJointMeasurement.CP.choiFactor, hc, CFC.sqrt_zero, Pi.zero_apply]
  rfl

theorem branchSquare_zero_of_component_zero (z : H × Ω) (q : HiddenColumn (Fin m))
    (hz : P.patchedComponentDensity q.1 z.1 z.2 = 0) : P.branchSquare z q = 0 := by
  simp only [branchSquare, QuantumProver.ElegantJointMeasurement.CP.positiveInputKraus,
    P.branchKraus_zero_of_component_zero z q hz, Matrix.conjTranspose_zero,
    Matrix.zero_mul, CFC.sqrt_zero]

theorem branchKraus_zero_of_off_tag (z : H × Ω) (q : HiddenColumn (Fin m))
    (hp : P.outputTag z ≠ q.1) : P.branchKraus z q = 0 :=
  P.branchKraus_zero_of_component_zero z q (P.patchedComponentDensity_zero_of_off_tag q.1 z hp)

theorem branchSquare_zero_of_off_tag (z : H × Ω) (q : HiddenColumn (Fin m))
    (hp : P.outputTag z ≠ q.1) : P.branchSquare z q = 0 :=
  P.branchSquare_zero_of_component_zero z q (P.patchedComponentDensity_zero_of_off_tag q.1 z hp)

theorem branchSquare_zero_of_not_commonValid (z : H × Ω) (q : HiddenColumn (Fin m))
    (hv : ¬ P.commonValid z) : P.branchSquare z q = 0 :=
  P.branchSquare_zero_of_component_zero z q
    (P.patchedComponentDensity_zero_of_not_commonValid q.1 z hv)

theorem countableRefinedSquare_zero_of_off_tag
    (z : H × (Ω × HiddenColumn (Fin m)))
    (hp : P.outputTag (z.1,z.2.1) ≠ z.2.2.1) : P.countableRefinedSquare z = 0 := by
  simp only [countableRefinedSquare, QuantumProver.ElegantJointMeasurement.ContinuousInstrumentQuadrature.weightedKraus,
    P.branchSquare_zero_of_off_tag _ _ hp, smul_zero]

theorem countableRefinedSquare_zero_of_not_commonValid
    (z : H × (Ω × HiddenColumn (Fin m)))
    (hv : ¬ P.commonValid (z.1,z.2.1)) : P.countableRefinedSquare z = 0 := by
  simp only [countableRefinedSquare, QuantumProver.ElegantJointMeasurement.ContinuousInstrumentQuadrature.weightedKraus,
    P.branchSquare_zero_of_not_commonValid _ _ hv, smul_zero]

end QuantumProver.ElegantJointMeasurement.ContinuousInstrumentRadonNikodym.CP.MatrixVaryingCPInstrument
