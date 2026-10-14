import Mathlib
import QuantumProver.InformationTheory.ElegantJointMeasurement.ContinuousCPInstruments

noncomputable section

open MeasureTheory ProbabilityTheory Matrix Set Filter
open scoped ENNReal BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace QuantumProver.ElegantJointMeasurement.ContinuousInstrumentRadonNikodym

set_option maxHeartbeats 800000

variable {H Ω Q : Type*} [MeasurableSpace H] [MeasurableSpace Ω]
  [Fintype Q] [DecidableEq Q]

def quadratic (v : Q → ℂ) (A : Matrix Q Q ℂ) : ℝ :=
  (star v ⬝ᵥ (A *ᵥ v)).re

def basisVector (a : Q) : Q → ℂ := Pi.single a 1

def quadraticComplexLinear (v : Q → ℂ) : Matrix Q Q ℂ →ₗ[ℂ] ℂ where
  toFun A := star v ⬝ᵥ (A *ᵥ v)
  map_add' A B := by simp [Matrix.add_mulVec, dotProduct_add]
  map_smul' c A := by simp [Matrix.smul_mulVec, dotProduct_smul]

def quadraticCLM (v : Q → ℂ) : Matrix Q Q ℂ →L[ℝ] ℝ :=
  Complex.reCLM.comp ((LinearMap.toContinuousLinearMap
    (quadraticComplexLinear v)).restrictScalars ℝ)

omit [DecidableEq Q] in
@[simp] theorem quadraticCLM_apply (v : Q → ℂ) (A : Matrix Q Q ℂ) :
    quadraticCLM v A = quadratic v A := rfl

@[simp] theorem quadratic_basisVector (A : Matrix Q Q ℂ) (a : Q) :
    quadratic (basisVector a) A = (A a a).re := by
  simp [quadratic, basisVector, dotProduct, Matrix.mulVec, Pi.single_apply]

omit [DecidableEq Q] in
theorem quadratic_nonneg (A : Matrix Q Q ℂ) (hA : A.PosSemidef) (v : Q → ℂ) :
    0 ≤ quadratic v A := by
  exact (Complex.nonneg_iff.mp (hA.dotProduct_mulVec_nonneg v)).1

structure PositiveChoiKernel where
  effect : H → Set Ω → Matrix Q Q ℂ
  positive : ∀ h s, MeasurableSet s → (effect h s).PosSemidef
  probe : (Q → ℂ) → Kernel H Ω
  probe_apply : ∀ v h s, MeasurableSet s →
    probe v h s = ENNReal.ofReal (quadratic v (effect h s))

namespace PositiveChoiKernel

variable (C : PositiveChoiKernel (H := H) (Ω := Ω) (Q := Q))

def traceKernel : Kernel H Ω := ∑ a, C.probe (basisVector a)

theorem traceKernel_apply (h : H) (s : Set Ω) (hs : MeasurableSet s) :
    C.traceKernel h s = ENNReal.ofReal (C.effect h s).trace.re := by
  simp only [traceKernel, Kernel.finsetSum_apply', C.probe_apply _ _ _ hs,
    quadratic_basisVector]
  rw [← ENNReal.ofReal_sum_of_nonneg]
  · simp [Matrix.trace, Matrix.diag]
  · intro a _
    simpa only [quadratic_basisVector] using
      quadratic_nonneg (C.effect h s) (C.positive h s hs) (basisVector a)

def probabilityKernel (d : ℝ) : Kernel H Ω where
  toFun h := (ENNReal.ofReal d)⁻¹ • C.traceKernel h
  measurable' := Measure.measurable_of_measurable_coe _ fun s hs => by
    simp only [Measure.smul_apply, smul_eq_mul]
    exact measurable_const.mul (C.traceKernel.measurable_coe hs)

theorem probabilityKernel_apply (d : ℝ) (h : H) (s : Set Ω)
    (hs : MeasurableSet s) :
    C.probabilityKernel d h s =
      (ENNReal.ofReal d)⁻¹ * ENNReal.ofReal (C.effect h s).trace.re := by
  change ((ENNReal.ofReal d)⁻¹ • C.traceKernel h) s = _
  rw [Measure.smul_apply, smul_eq_mul, C.traceKernel_apply h s hs]

theorem probabilityKernel_isMarkov (d : ℝ) (hd : 0 < d)
    (htotal : ∀ h, (C.effect h univ).trace.re = d) :
    IsMarkovKernel (C.probabilityKernel d) := by
  constructor
  intro h
  constructor
  rw [C.probabilityKernel_apply d h univ MeasurableSet.univ, htotal]
  exact ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.mpr hd).ne' ENNReal.ofReal_ne_top

theorem probe_isFinite (d : ℝ) (htotal : ∀ h, (C.effect h univ).trace.re = d)
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
      simpa [htotal h] using QuantumProver.ElegantJointMeasurement.ContinuousCPInstruments.posSemidef_norm_le_trace
        (C.effect h univ) (C.positive h univ MeasurableSet.univ)

theorem probe_absolutelyContinuous (d : ℝ) (v : Q → ℂ) (h : H) :
    C.probe v h ≪ C.probabilityKernel d h := by
  refine Measure.AbsolutelyContinuous.mk fun s hs hzero => ?_
  rw [C.probabilityKernel_apply d h s hs] at hzero
  have htrace : (C.effect h s).trace.re ≤ 0 := by
    apply ENNReal.ofReal_eq_zero.mp
    exact (mul_eq_zero.mp hzero).resolve_left
      (by simp only [ENNReal.inv_eq_zero, ENNReal.ofReal_ne_top, not_false_eq_true])
  have hnorm : ‖C.effect h s‖ ≤ 0 :=
    (QuantumProver.ElegantJointMeasurement.ContinuousCPInstruments.posSemidef_norm_le_trace
      (C.effect h s) (C.positive h s hs)).trans htrace
  have heffect : C.effect h s = 0 := norm_eq_zero.mp (le_antisymm hnorm (norm_nonneg _))
  rw [C.probe_apply v h s hs, heffect]
  simp [quadratic]

variable [MeasurableSpace.CountableOrCountablyGenerated H Ω]

def probeDensity (d : ℝ) (v : Q → ℂ) (h : H) (ω : Ω) : ℝ :=
  ((C.probe v).rnDeriv (C.probabilityKernel d) h ω).toReal

@[fun_prop] theorem measurable_probeDensity (d : ℝ) (v : Q → ℂ) :
    Measurable (fun z : H × Ω => C.probeDensity d v z.1 z.2) := by
  exact ((C.probe v).measurable_rnDeriv (C.probabilityKernel d)).ennreal_toReal

theorem probeDensity_nonneg (d : ℝ) (v : Q → ℂ) (h : H) (ω : Ω) :
    0 ≤ C.probeDensity d v h ω := ENNReal.toReal_nonneg

theorem integrable_probeDensity (d : ℝ) (hd : 0 < d)
    (htotal : ∀ h, (C.effect h univ).trace.re = d) (v : Q → ℂ) (h : H) :
    Integrable (C.probeDensity d v h) (C.probabilityKernel d h) := by
  have : IsFiniteKernel (C.probe v) := C.probe_isFinite d htotal v
  have : IsMarkovKernel (C.probabilityKernel d) := C.probabilityKernel_isMarkov d hd htotal
  apply integrable_toReal_of_lintegral_ne_top
    (((C.probe v).measurable_rnDeriv (C.probabilityKernel d)).of_uncurry_left.aemeasurable)
  rw [Kernel.lintegral_rnDeriv (C.probe_absolutelyContinuous d v h)]
  exact measure_ne_top _ _

theorem setIntegral_probeDensity (d : ℝ) (hd : 0 < d)
    (htotal : ∀ h, (C.effect h univ).trace.re = d) (v : Q → ℂ)
    (h : H) (s : Set Ω) (hs : MeasurableSet s) :
    (∫ ω in s, C.probeDensity d v h ω ∂C.probabilityKernel d h) =
      quadratic v (C.effect h s) := by
  have : IsFiniteKernel (C.probe v) := C.probe_isFinite d htotal v
  have : IsMarkovKernel (C.probabilityKernel d) := C.probabilityKernel_isMarkov d hd htotal
  change (∫ ω in s, ((C.probe v).rnDeriv (C.probabilityKernel d) h ω).toReal
    ∂C.probabilityKernel d h) = _
  rw [integral_toReal
    (((C.probe v).measurable_rnDeriv (C.probabilityKernel d)).of_uncurry_left.aemeasurable.restrict)
    (ae_restrict_of_ae (Kernel.rnDeriv_lt_top (C.probe v) (C.probabilityKernel d)))]
  rw [Kernel.setLIntegral_rnDeriv (C.probe_absolutelyContinuous d v h) hs,
    C.probe_apply v h s hs, ENNReal.toReal_ofReal (quadratic_nonneg _ (C.positive h s hs) v)]

end PositiveChoiKernel

def polarizationEntry (f : (Q → ℂ) → ℝ) (a b : Q) : ℂ :=
  (((f (basisVector a + basisVector b) - f (basisVector a) - f (basisVector b)) / 2 : ℝ) : ℂ) +
    (((f (basisVector a) + f (basisVector b) -
      f (basisVector a + Complex.I • basisVector b)) / 2 : ℝ) : ℂ) * Complex.I

theorem polarization_quadratic (A : Matrix Q Q ℂ) (hA : A.IsHermitian) (a b : Q) :
    polarizationEntry (fun v => quadratic v A) a b = A a b := by
  have hba : A b a = star (A a b) := (hA.apply b a).symm
  simp only [polarizationEntry, quadratic, star_add, star_smul, Matrix.mulVec_add,
    Matrix.mulVec_smul, add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul]
  simp [basisVector, dotProduct, Matrix.mulVec, Pi.single_apply, hba]
  apply Complex.ext <;> simp <;> ring

theorem matrix_eq_sum_smul_single (A : Matrix Q Q ℂ) :
    A = ∑ a, ∑ b, A a b • Matrix.single a b 1 := by
  simpa using Matrix.matrix_eq_sum_single A

omit [Fintype Q] in
theorem integral_polarizationEntry {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (f : X → (Q → ℂ) → ℝ) (hf : ∀ v, Integrable (fun x => f x v) μ) (a b : Q) :
    (∫ x, polarizationEntry (f x) a b ∂μ) =
      polarizationEntry (fun v => ∫ x, f x v ∂μ) a b := by
  have hr := (((hf (basisVector a + basisVector b)).sub (hf (basisVector a))).sub
    (hf (basisVector b))).div_const 2
  have hi := (((hf (basisVector a)).add (hf (basisVector b))).sub
    (hf (basisVector a + Complex.I • basisVector b))).div_const 2
  dsimp only [Pi.sub_apply, Pi.add_apply] at hr hi
  unfold polarizationEntry
  have hrC : Integrable (fun x => (((f x (basisVector a + basisVector b) -
      f x (basisVector a) - f x (basisVector b)) / 2 : ℝ) : ℂ)) μ := hr.ofReal
  have hiC : Integrable (fun x => (((f x (basisVector a) + f x (basisVector b) -
      f x (basisVector a + Complex.I • basisVector b)) / 2 : ℝ) : ℂ)) μ := hi.ofReal
  calc
    _ = (∫ x, (((f x (basisVector a + basisVector b) - f x (basisVector a) -
        f x (basisVector b)) / 2 : ℝ) : ℂ) ∂μ) +
        ∫ x, (((f x (basisVector a) + f x (basisVector b) -
          f x (basisVector a + Complex.I • basisVector b)) / 2 : ℝ) : ℂ) * Complex.I ∂μ :=
      integral_add hrC (hiC.mul_const Complex.I)
    _ = _ := by
      erw [integral_complex_ofReal, integral_mul_const Complex.I, integral_complex_ofReal, integral_div,
    integral_sub ((hf (basisVector a + basisVector b)).sub (hf (basisVector a)))
      (hf (basisVector b)),
    integral_sub (hf (basisVector a + basisVector b)) (hf (basisVector a)),
    integral_div, integral_sub ((hf (basisVector a)).add (hf (basisVector b)))
      (hf (basisVector a + Complex.I • basisVector b)),
    integral_add (hf (basisVector a)) (hf (basisVector b))]

namespace PositiveChoiKernel

variable (C : PositiveChoiKernel (H := H) (Ω := Ω) (Q := Q))
variable [MeasurableSpace.CountableOrCountablyGenerated H Ω]

def density (d : ℝ) (h : H) (ω : Ω) : Matrix Q Q ℂ :=
  fun a b => polarizationEntry (fun v => C.probeDensity d v h ω) a b

theorem measurable_density (d : ℝ) :
    Measurable (fun z : H × Ω => C.density d z.1 z.2) := by
  apply Measurable.of_eval
  intro a
  apply Measurable.of_eval
  intro b
  simp only [density, polarizationEntry]
  fun_prop

theorem integrable_density_entry (d : ℝ) (hd : 0 < d)
    (htotal : ∀ h, (C.effect h univ).trace.re = d) (h : H) (a b : Q) :
    Integrable (fun ω => C.density d h ω a b) (C.probabilityKernel d h) := by
  have hp := C.integrable_probeDensity d hd htotal
  exact (((hp (basisVector a + basisVector b) h).sub (hp (basisVector a) h)).sub
    (hp (basisVector b) h)).div_const 2 |>.ofReal |>.add
      ((((hp (basisVector a) h).add (hp (basisVector b) h)).sub
        (hp (basisVector a + Complex.I • basisVector b) h)).div_const 2 |>.ofReal
          |>.mul_const Complex.I)

theorem integrable_density (d : ℝ) (hd : 0 < d)
    (htotal : ∀ h, (C.effect h univ).trace.re = d) (h : H) :
    Integrable (C.density d h) (C.probabilityKernel d h) := by
  have heq : C.density d h = fun ω => ∑ a, ∑ b,
      C.density d h ω a b • Matrix.single a b 1 := by
    funext ω
    exact matrix_eq_sum_smul_single _
  rw [heq]
  exact integrable_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ =>
    (C.integrable_density_entry d hd htotal h a b).smul_const _

theorem setIntegral_density_entry (d : ℝ) (hd : 0 < d)
    (htotal : ∀ h, (C.effect h univ).trace.re = d) (h : H)
    (s : Set Ω) (hs : MeasurableSet s) (a b : Q) :
    (∫ ω in s, C.density d h ω a b ∂C.probabilityKernel d h) = C.effect h s a b := by
  change (∫ ω in s, polarizationEntry (fun v => C.probeDensity d v h ω) a b
    ∂C.probabilityKernel d h) = _
  rw [integral_polarizationEntry _ _
    (fun v => (C.integrable_probeDensity d hd htotal v h).integrableOn)]
  simp_rw [C.setIntegral_probeDensity d hd htotal _ h s hs]
  exact polarization_quadratic _ (C.positive h s hs).isHermitian a b

theorem setIntegral_density (d : ℝ) (hd : 0 < d)
    (htotal : ∀ h, (C.effect h univ).trace.re = d) (h : H)
    (s : Set Ω) (hs : MeasurableSet s) :
    (∫ ω in s, C.density d h ω ∂C.probabilityKernel d h) = C.effect h s := by
  have heq : C.density d h = fun ω => ∑ a, ∑ b,
      C.density d h ω a b • Matrix.single a b 1 := by
    funext ω
    exact matrix_eq_sum_smul_single _
  rw [heq]
  calc
    _ = ∑ a, ∫ ω in s, (∑ b, C.density d h ω a b • Matrix.single a b (1 : ℂ))
        ∂C.probabilityKernel d h := integral_finsetSum _ fun a _ =>
          integrable_finsetSum _ fun b _ =>
            (C.integrable_density_entry d hd htotal h a b).integrableOn.smul_const _
    _ = ∑ a, ∑ b, (∫ ω in s, C.density d h ω a b ∂C.probabilityKernel d h) •
        Matrix.single a b (1 : ℂ) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [integral_finsetSum _ (fun b _ =>
        (C.integrable_density_entry d hd htotal h a b).integrableOn.smul_const _)]
      simp only [integral_smul_const]
    _ = C.effect h s := by
      simp_rw [C.setIntegral_density_entry d hd htotal h s hs]
      exact (matrix_eq_sum_smul_single _).symm

theorem ae_density_isHermitian (d : ℝ) (hd : 0 < d)
    (htotal : ∀ h, (C.effect h univ).trace.re = d) (h : H) :
    ∀ᵐ ω ∂C.probabilityKernel d h, (C.density d h ω).IsHermitian := by
  have hentry (a b : Q) : ∀ᵐ ω ∂C.probabilityKernel d h,
      star (C.density d h ω b a) = C.density d h ω a b := by
    have hstar : Integrable (fun ω => star (C.density d h ω b a))
        (C.probabilityKernel d h) :=
      (RCLike.conjLIE (K := ℂ)).toContinuousLinearEquiv.toContinuousLinearMap.integrable_comp
        (C.integrable_density_entry d hd htotal h b a)
    apply Integrable.ae_eq_of_forall_setIntegral_eq _ _ hstar
      (C.integrable_density_entry d hd htotal h a b)
    intro s hs _
    change (∫ ω in s, star (C.density d h ω b a) ∂C.probabilityKernel d h) = _
    erw [integral_conj, C.setIntegral_density_entry d hd htotal h s hs,
      C.setIntegral_density_entry d hd htotal h s hs]
    exact (C.positive h s hs).isHermitian.apply a b
  filter_upwards [ae_all_iff.mpr (fun a => ae_all_iff.mpr (hentry a))] with ω hω
  exact Matrix.IsHermitian.ext hω

theorem ae_density_quadratic_nonneg (d : ℝ) (hd : 0 < d)
    (htotal : ∀ h, (C.effect h univ).trace.re = d) (h : H) (v : Q → ℂ) :
    ∀ᵐ ω ∂C.probabilityKernel d h, 0 ≤ quadratic v (C.density d h ω) := by
  apply ae_nonneg_of_forall_setIntegral_nonneg
    ((quadraticCLM v).integrable_comp (C.integrable_density d hd htotal h))
  intro s hs _
  have hcomm := (quadraticCLM v).integral_comp_comm (μ := (C.probabilityKernel d h).restrict s)
    (C.integrable_density d hd htotal h).integrableOn
  change 0 ≤ ∫ ω in s, quadraticCLM v (C.density d h ω) ∂C.probabilityKernel d h
  rw [hcomm, C.setIntegral_density d hd htotal h s hs]
  exact quadratic_nonneg _ (C.positive h s hs) v

theorem ae_density_posSemidef (d : ℝ) (hd : 0 < d)
    (htotal : ∀ h, (C.effect h univ).trace.re = d) (h : H) :
    ∀ᵐ ω ∂C.probabilityKernel d h, (C.density d h ω).PosSemidef := by
  let u : ℕ → (Q → ℂ) := TopologicalSpace.denseSeq (Q → ℂ)
  have hu : DenseRange u := TopologicalSpace.denseRange_denseSeq _
  filter_upwards [C.ae_density_isHermitian d hd htotal h,
    ae_all_iff.mpr (fun n => C.ae_density_quadratic_nonneg d hd htotal h (u n))]
    with ω hherm hpos
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hherm
  intro v
  have hv : 0 ≤ quadratic v (C.density d h ω) := by
    apply hu.induction_on (p := fun x => 0 ≤ quadratic x (C.density d h ω)) v
    · apply isClosed_le continuous_const
      unfold quadratic
      simp only [dotProduct, Matrix.mulVec]
      fun_prop
    · exact hpos
  exact Complex.nonneg_iff.mpr ⟨hv,
    (hherm.im_star_dotProduct_mulVec_self v).symm⟩

def positiveDensity (d : ℝ) (h : H) (ω : Ω) : Matrix Q Q ℂ :=
  by
    classical
    exact if (C.density d h ω).PosSemidef then C.density d h ω else 0

theorem measurable_positiveDensity (d : ℝ) :
    Measurable (fun z : H × Ω => C.positiveDensity d z.1 z.2) := by
  classical
  exact (C.measurable_density d).piecewise
    (Matrix.posSemidef_is_closed.measurableSet.preimage (C.measurable_density d)) measurable_const

theorem positiveDensity_posSemidef (d : ℝ) (h : H) (ω : Ω) :
    (C.positiveDensity d h ω).PosSemidef := by
  classical
  unfold positiveDensity
  split_ifs with hp
  · exact hp
  · exact Matrix.PosSemidef.zero

theorem positiveDensity_ae_eq (d : ℝ) (hd : 0 < d)
    (htotal : ∀ h, (C.effect h univ).trace.re = d) (h : H) :
    C.positiveDensity d h =ᵐ[C.probabilityKernel d h] C.density d h := by
  filter_upwards [C.ae_density_posSemidef d hd htotal h] with ω hω
  simp [positiveDensity, hω]

theorem integrable_positiveDensity (d : ℝ) (hd : 0 < d)
    (htotal : ∀ h, (C.effect h univ).trace.re = d) (h : H) :
    Integrable (C.positiveDensity d h) (C.probabilityKernel d h) :=
  (C.integrable_density d hd htotal h).congr (C.positiveDensity_ae_eq d hd htotal h).symm

theorem setIntegral_positiveDensity (d : ℝ) (hd : 0 < d)
    (htotal : ∀ h, (C.effect h univ).trace.re = d) (h : H)
    (s : Set Ω) (hs : MeasurableSet s) :
    (∫ ω in s, C.positiveDensity d h ω ∂C.probabilityKernel d h) = C.effect h s := by
  rw [integral_congr_ae (ae_restrict_of_ae (C.positiveDensity_ae_eq d hd htotal h))]
  exact C.setIntegral_density d hd htotal h s hs

end PositiveChoiKernel

def traceReCLM : Matrix Q Q ℂ →L[ℝ] ℝ := ∑ a, quadraticCLM (basisVector a)

@[simp] theorem traceReCLM_apply (A : Matrix Q Q ℂ) :
    traceReCLM A = A.trace.re := by
  simp [traceReCLM, Matrix.trace, Matrix.diag]

namespace PositiveChoiKernel

variable (C : PositiveChoiKernel (H := H) (Ω := Ω) (Q := Q))
variable [MeasurableSpace.CountableOrCountablyGenerated H Ω]

omit [MeasurableSpace.CountableOrCountablyGenerated H Ω] in
theorem trace_eq_mass (d : ℝ) (hd : 0 < d) (h : H)
    (s : Set Ω) (hs : MeasurableSet s) :
    (C.effect h s).trace.re = d * (C.probabilityKernel d h).real s := by
  have ht : 0 ≤ (C.effect h s).trace.re :=
    (norm_nonneg _).trans (QuantumProver.ElegantJointMeasurement.ContinuousCPInstruments.posSemidef_norm_le_trace
      _ (C.positive h s hs))
  rw [measureReal_def, C.probabilityKernel_apply d h s hs,
    ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_ofReal hd.le,
    ENNReal.toReal_ofReal ht]
  field_simp

theorem ae_positiveDensity_trace (d : ℝ) (hd : 0 < d)
    (htotal : ∀ h, (C.effect h univ).trace.re = d) (h : H) :
    ∀ᵐ ω ∂C.probabilityKernel d h, (C.positiveDensity d h ω).trace.re = d := by
  have : IsMarkovKernel (C.probabilityKernel d) := C.probabilityKernel_isMarkov d hd htotal
  have ht := (traceReCLM (Q := Q)).integrable_comp (C.integrable_positiveDensity d hd htotal h)
  simp only [← traceReCLM_apply]
  apply Integrable.ae_eq_of_forall_setIntegral_eq _ _ ht (integrable_const d)
  intro s hs _
  rw [(traceReCLM (Q := Q)).integral_comp_comm (μ := (C.probabilityKernel d h).restrict s)
      (C.integrable_positiveDensity d hd htotal h).integrableOn,
    C.setIntegral_positiveDensity d hd htotal h s hs, traceReCLM_apply,
    setIntegral_const, smul_eq_mul, C.trace_eq_mass d hd h s hs]
  exact mul_comm _ _

theorem exists_joint_positive_density (d : ℝ) (hd : 0 < d)
    (htotal : ∀ h, (C.effect h univ).trace.re = d) :
    ∃ μ : Kernel H Ω, IsMarkovKernel μ ∧
      ∃ D : H → Ω → Matrix Q Q ℂ,
        Measurable (fun z : H × Ω => D z.1 z.2) ∧
        (∀ h ω, (D h ω).PosSemidef) ∧
        (∀ h, Integrable (D h) (μ h)) ∧
        (∀ h s, MeasurableSet s → (∫ ω in s, D h ω ∂μ h) = C.effect h s) ∧
        (∀ h, ∀ᵐ ω ∂μ h, (D h ω).trace.re = d) ∧
        (∀ h s, MeasurableSet s → μ h s =
          (ENNReal.ofReal d)⁻¹ * ENNReal.ofReal (C.effect h s).trace.re) := by
  exact ⟨C.probabilityKernel d, C.probabilityKernel_isMarkov d hd htotal,
    C.positiveDensity d, C.measurable_positiveDensity d, C.positiveDensity_posSemidef d,
    C.integrable_positiveDensity d hd htotal, C.setIntegral_positiveDensity d hd htotal,
    C.ae_positiveDensity_trace d hd htotal, C.probabilityKernel_apply d⟩

end PositiveChoiKernel

structure CoordinateChoiKernel where
  effect : H → Set Ω → Matrix Q Q ℂ
  empty : ∀ h, effect h ∅ = 0
  positive : ∀ h s, MeasurableSet s → (effect h s).PosSemidef
  measurable_entry : ∀ s, MeasurableSet s → ∀ a b,
    Measurable (fun h => effect h s a b)
  coordinate_additive : ∀ h (s : ℕ → Set Ω), (∀ n, MeasurableSet (s n)) →
    Pairwise (fun i j => Disjoint (s i) (s j)) → ∀ a b,
      HasSum (fun n => effect h (s n) a b) (effect h (⋃ n, s n) a b)

namespace CoordinateChoiKernel

variable (C : CoordinateChoiKernel (H := H) (Ω := Ω) (Q := Q))

theorem matrix_additive (h : H) (s : ℕ → Set Ω) (hs : ∀ n, MeasurableSet (s n))
    (hdisj : Pairwise (fun i j => Disjoint (s i) (s j))) :
    HasSum (fun n => C.effect h (s n)) (C.effect h (⋃ n, s n)) := by
  have hb := hasSum_sum (s := Finset.univ) (fun a _ =>
    hasSum_sum (s := Finset.univ) (fun b _ =>
      (C.coordinate_additive h s hs hdisj a b).smul_const (Matrix.single a b (1 : ℂ))))
  simpa only [← matrix_eq_sum_smul_single] using hb

theorem quadratic_additive (v : Q → ℂ) (h : H) (s : ℕ → Set Ω)
    (hs : ∀ n, MeasurableSet (s n)) (hdisj : Pairwise (fun i j => Disjoint (s i) (s j))) :
    HasSum (fun n => quadratic v (C.effect h (s n)))
      (quadratic v (C.effect h (⋃ n, s n))) :=
  (quadraticCLM v).hasSum (C.matrix_additive h s hs hdisj)

def probeMeasure (v : Q → ℂ) (h : H) : Measure Ω :=
  Measure.ofMeasurable (fun s _ => ENNReal.ofReal (quadratic v (C.effect h s)))
    (by simp [C.empty, quadratic])
    (fun s hs hdisj => by
      have hsum := C.quadratic_additive v h s hs hdisj
      rw [← hsum.tsum_eq]
      exact ENNReal.ofReal_tsum_of_nonneg
        (fun n => quadratic_nonneg _ (C.positive h (s n) (hs n)) v) hsum.summable)

theorem probeMeasure_apply (v : Q → ℂ) (h : H) (s : Set Ω) (hs : MeasurableSet s) :
    C.probeMeasure v h s = ENNReal.ofReal (quadratic v (C.effect h s)) :=
  Measure.ofMeasurable_apply s hs

def probeKernel (v : Q → ℂ) : Kernel H Ω where
  toFun h := C.probeMeasure v h
  measurable' := Measure.measurable_of_measurable_coe _ fun s hs => by
    simp_rw [C.probeMeasure_apply v _ s hs]
    have hm : Measurable (fun h => C.effect h s) :=
      Measurable.of_eval fun a => Measurable.of_eval fun b => C.measurable_entry s hs a b
    exact ((quadraticCLM v).continuous.measurable.comp hm).ennreal_ofReal

def toPositiveChoiKernel : PositiveChoiKernel (H := H) (Ω := Ω) (Q := Q) where
  effect := C.effect
  positive := C.positive
  probe := C.probeKernel
  probe_apply v h s hs := C.probeMeasure_apply v h s hs

variable [MeasurableSpace.CountableOrCountablyGenerated H Ω]

theorem exists_joint_positive_density (d : ℝ) (hd : 0 < d)
    (htotal : ∀ h, (C.effect h univ).trace.re = d) :
    ∃ μ : Kernel H Ω, IsMarkovKernel μ ∧
      ∃ D : H → Ω → Matrix Q Q ℂ,
        Measurable (fun z : H × Ω => D z.1 z.2) ∧
        (∀ h ω, (D h ω).PosSemidef) ∧
        (∀ h, Integrable (D h) (μ h)) ∧
        (∀ h s, MeasurableSet s → (∫ ω in s, D h ω ∂μ h) = C.effect h s) ∧
        (∀ h, ∀ᵐ ω ∂μ h, (D h ω).trace.re = d) ∧
        (∀ h s, MeasurableSet s → μ h s =
          (ENNReal.ofReal d)⁻¹ * ENNReal.ofReal (C.effect h s).trace.re) :=
  C.toPositiveChoiKernel.exists_joint_positive_density d hd htotal

end CoordinateChoiKernel

section CP

variable {I O : Type*} [Fintype I] [Fintype O] [DecidableEq I] [DecidableEq O]

def fromChoi (A : Matrix (I × O) (I × O) ℂ) :
    Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ where
  toFun X := fun b c => ∑ i, ∑ j, X i j * A (i, b) (j, c)
  map_add' X Y := by
    ext b c
    change (∑ i, ∑ j, (X i j + Y i j) * A (i, b) (j, c)) =
      (∑ i, ∑ j, X i j * A (i, b) (j, c)) + ∑ i, ∑ j, Y i j * A (i, b) (j, c)
    simp [add_mul, Finset.sum_add_distrib]
  map_smul' z X := by
    ext b c
    change (∑ i, ∑ j, (z * X i j) * A (i, b) (j, c)) =
      z * ∑ i, ∑ j, X i j * A (i, b) (j, c)
    simp [Finset.mul_sum, mul_assoc]

omit [Fintype O] [DecidableEq O] in
theorem fromChoi_matrix_unit (A : Matrix (I × O) (I × O) ℂ)
    (i j : I) (b c : O) :
    fromChoi A (Matrix.single i j 1) b c = A (i, b) (j, c) := by
  change (∑ k, ∑ l, Matrix.single i j (1 : ℂ) k l * A (k, b) (l, c)) = _
  simp [Matrix.single_apply, ite_and]

theorem fromChoi_choi (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) :
    fromChoi (QuantumProver.ElegantJointMeasurement.CP.choi Φ) = Φ := by
  apply QuantumProver.ElegantJointMeasurement.CP.linearMap_eq_of_matrix_units
  intro i j
  ext b c
  rw [fromChoi_matrix_unit]
  rfl

omit [Fintype O] [DecidableEq O] in
theorem choi_fromChoi (A : Matrix (I × O) (I × O) ℂ) :
    QuantumProver.ElegantJointMeasurement.CP.choi (fromChoi A) = A := by
  ext a b
  exact fromChoi_matrix_unit A a.1 b.1 a.2 b.2

theorem fromChoi_completelyPositive (A : Matrix (I × O) (I × O) ℂ)
    (hA : A.PosSemidef) : QuantumProver.ElegantJointMeasurement.CP.CompletelyPositive (fromChoi A) := by
  let K : I × O → Matrix O I ℂ := fun q b i => CFC.sqrt A (i, b) q
  have hs : (CFC.sqrt A)ᴴ = CFC.sqrt A :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)).isHermitian
  have hfactor : CFC.sqrt A * (CFC.sqrt A)ᴴ = A := by
    rw [hs, ← pow_two]
    exact CFC.sq_sqrt A hA.nonneg
  have heq : fromChoi A = QuantumProver.ElegantJointMeasurement.CP.krausMap K := by
    apply QuantumProver.ElegantJointMeasurement.CP.linearMap_eq_of_matrix_units
    intro i j
    ext b c
    rw [fromChoi_matrix_unit]
    change A (i, b) (j, c) = (∑ q, K q * Matrix.single i j (1 : ℂ) * (K q)ᴴ) b c
    simp only [Matrix.sum_apply, QuantumProver.ElegantJointMeasurement.CP.kraus_matrix_unit]
    change A (i, b) (j, c) = (CFC.sqrt A * (CFC.sqrt A)ᴴ) (i, b) (j, c)
    rw [hfactor]
  rw [heq]
  exact QuantumProver.ElegantJointMeasurement.CP.krausMap_completelyPositive K

def choiReadoutLinear (X : Matrix I I ℂ) :
    Matrix (I × O) (I × O) ℂ →ₗ[ℂ] Matrix O O ℂ where
  toFun A := fromChoi A X
  map_add' A B := by
    ext b c
    change (∑ i, ∑ j, X i j * (A (i, b) (j, c) + B (i, b) (j, c))) =
      (∑ i, ∑ j, X i j * A (i, b) (j, c)) + ∑ i, ∑ j, X i j * B (i, b) (j, c)
    simp [mul_add, Finset.sum_add_distrib]
  map_smul' z A := by
    ext b c
    change (∑ i, ∑ j, X i j * (z * A (i, b) (j, c))) =
      z * ∑ i, ∑ j, X i j * A (i, b) (j, c)
    simp [Finset.mul_sum, mul_left_comm]

def choiReadoutCLM (X : Matrix I I ℂ) :
    Matrix (I × O) (I × O) ℂ →L[ℂ] Matrix O O ℂ :=
  LinearMap.toContinuousLinearMap (choiReadoutLinear X)

omit [DecidableEq I] [DecidableEq O] in
@[simp] theorem choiReadoutCLM_apply (X : Matrix I I ℂ)
    (A : Matrix (I × O) (I × O) ℂ) : choiReadoutCLM X A = fromChoi A X := rfl

structure MatrixCPInstrument where
  map : H → Set Ω → (Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ)
  empty : ∀ h, map h ∅ = 0
  completelyPositive : ∀ h s, MeasurableSet s → QuantumProver.ElegantJointMeasurement.CP.CompletelyPositive (map h s)
  measurable_entry : ∀ s, MeasurableSet s → ∀ i j b c,
    Measurable (fun h => map h s (Matrix.single i j 1) b c)
  coordinate_additive : ∀ h (s : ℕ → Set Ω), (∀ n, MeasurableSet (s n)) →
    Pairwise (fun i j => Disjoint (s i) (s j)) → ∀ i j b c,
      HasSum (fun n => map h (s n) (Matrix.single i j 1) b c)
        (map h (⋃ n, s n) (Matrix.single i j 1) b c)
  traceComplete : ∀ h X, (map h univ X).trace = X.trace

namespace MatrixCPInstrument

variable (P : MatrixCPInstrument (H := H) (Ω := Ω) (I := I) (O := O))

def choiKernel : CoordinateChoiKernel (H := H) (Ω := Ω) (Q := I × O) where
  effect h s := QuantumProver.ElegantJointMeasurement.CP.choi (P.map h s)
  empty h := by
    ext a b
    change P.map h ∅ (Matrix.single a.1 b.1 1) a.2 b.2 = 0
    rw [P.empty]
    rfl
  positive h s hs := QuantumProver.ElegantJointMeasurement.CP.choi_posSemidef _ (P.completelyPositive h s hs)
  measurable_entry s hs a b := P.measurable_entry s hs a.1 b.1 a.2 b.2
  coordinate_additive h s hs hdisj a b := P.coordinate_additive h s hs hdisj a.1 b.1 a.2 b.2

theorem choiKernel_totalTrace (h : H) :
    (P.choiKernel.effect h univ).trace.re = (Fintype.card I : ℝ) := by
  change (QuantumProver.ElegantJointMeasurement.CP.choi (P.map h univ)).trace.re = _
  rw [QuantumProver.ElegantJointMeasurement.ContinuousCPInstruments.choi_trace, P.traceComplete]
  simp

variable [Nonempty I] [MeasurableSpace.CountableOrCountablyGenerated H Ω]

def measureKernel : Kernel H Ω :=
  P.choiKernel.toPositiveChoiKernel.probabilityKernel (Fintype.card I)

def cpDensity (h : H) (ω : Ω) : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ :=
  fromChoi (P.choiKernel.toPositiveChoiKernel.positiveDensity (Fintype.card I) h ω)

omit [MeasurableSpace.CountableOrCountablyGenerated H Ω] in
theorem measureKernel_isMarkov : IsMarkovKernel P.measureKernel :=
  P.choiKernel.toPositiveChoiKernel.probabilityKernel_isMarkov
    (Fintype.card I) (by exact_mod_cast Fintype.card_pos) P.choiKernel_totalTrace

omit [Nonempty I] in
theorem cpDensity_completelyPositive (h : H) (ω : Ω) :
    QuantumProver.ElegantJointMeasurement.CP.CompletelyPositive (P.cpDensity h ω) :=
  fromChoi_completelyPositive _
    (P.choiKernel.toPositiveChoiKernel.positiveDensity_posSemidef (Fintype.card I) h ω)

omit [Nonempty I] in
theorem cpDensity_joint_coordinate_measurable (i j : I) (b c : O) :
    Measurable (fun z : H × Ω => P.cpDensity z.1 z.2 (Matrix.single i j 1) b c) := by
  simp only [cpDensity, fromChoi_matrix_unit]
  exact (measurable_pi_iff.mp (measurable_pi_iff.mp
    (P.choiKernel.toPositiveChoiKernel.measurable_positiveDensity (Fintype.card I)) (i, b))) (j, c)

omit [Nonempty I] in
theorem cpDensity_coordinateMeasurable (h : H) :
    QuantumProver.ElegantJointMeasurement.ContinuousCPInstruments.CoordinateMeasurable (P.cpDensity h) := by
  change ∀ (i j : I) (b c : O),
    Measurable (fun ω : Ω => P.cpDensity h ω (Matrix.single i j (1 : ℂ)) b c)
  intro i j b c
  exact Measurable.of_uncurry_left
    (f := fun h' : H => fun ω : Ω =>
      P.cpDensity h' ω (Matrix.single i j (1 : ℂ)) b c)
    (x := h) (P.cpDensity_joint_coordinate_measurable i j b c)

theorem cpDensity_integrable (h : H) (X : Matrix I I ℂ) :
    Integrable (fun ω => P.cpDensity h ω X) (P.measureKernel h) :=
  (choiReadoutCLM X).integrable_comp
    (P.choiKernel.toPositiveChoiKernel.integrable_positiveDensity
      (Fintype.card I) (by exact_mod_cast Fintype.card_pos) P.choiKernel_totalTrace h)

theorem cpDensity_setIntegral (h : H) (s : Set Ω) (hs : MeasurableSet s)
    (X : Matrix I I ℂ) :
    (∫ ω in s, P.cpDensity h ω X ∂P.measureKernel h) = P.map h s X := by
  have hcomm := (choiReadoutCLM X).integral_comp_comm
    (μ := (P.measureKernel h).restrict s)
    (P.choiKernel.toPositiveChoiKernel.integrable_positiveDensity
      (Fintype.card I) (by exact_mod_cast Fintype.card_pos) P.choiKernel_totalTrace h).integrableOn
  change (∫ ω in s, choiReadoutCLM X
    (P.choiKernel.toPositiveChoiKernel.positiveDensity (Fintype.card I) h ω)
    ∂P.measureKernel h) = _
  rw [hcomm]
  change choiReadoutCLM X (∫ ω in s,
    P.choiKernel.toPositiveChoiKernel.positiveDensity (Fintype.card I) h ω
    ∂P.choiKernel.toPositiveChoiKernel.probabilityKernel (Fintype.card I) h) = _
  rw [P.choiKernel.toPositiveChoiKernel.setIntegral_positiveDensity
    (Fintype.card I) (by exact_mod_cast Fintype.card_pos) P.choiKernel_totalTrace h s hs]
  change fromChoi (QuantumProver.ElegantJointMeasurement.CP.choi (P.map h s)) X = _
  rw [fromChoi_choi]

theorem cpDensity_matrixTraceComplete (h : H) :
    QuantumProver.ElegantJointMeasurement.ContinuousCPInstruments.MatrixTraceComplete (P.measureKernel h) (P.cpDensity h) := by
  intro X
  let T : Matrix O O ℂ →L[ℂ] ℂ := LinearMap.toContinuousLinearMap (Matrix.traceLinearMap O ℂ ℂ)
  have ht := (T.integral_comp_comm (P.cpDensity_integrable h X)).symm
  change (∫ ω, P.cpDensity h ω X ∂P.measureKernel h).trace =
    ∫ ω, (P.cpDensity h ω X).trace ∂P.measureKernel h at ht
  have hi : (∫ ω, P.cpDensity h ω X ∂P.measureKernel h) = P.map h univ X := by
    simpa only [Measure.restrict_univ] using P.cpDensity_setIntegral h univ MeasurableSet.univ X
  rw [← ht, hi]
  exact P.traceComplete h X

theorem cpDensity_choi_trace (h : H) :
    ∀ᵐ ω ∂P.measureKernel h,
      (QuantumProver.ElegantJointMeasurement.CP.choi (P.cpDensity h ω)).trace.re = (Fintype.card I : ℝ) := by
  simp only [cpDensity, choi_fromChoi]
  exact P.choiKernel.toPositiveChoiKernel.ae_positiveDensity_trace
    (Fintype.card I) (by exact_mod_cast Fintype.card_pos) P.choiKernel_totalTrace h

theorem integral_canonicalGram_eq_one (h : H) :
    (∫ ω, QuantumProver.ElegantJointMeasurement.ContinuousCPInstruments.canonicalGram (P.cpDensity h) ω
      ∂P.measureKernel h) = 1 :=
  QuantumProver.ElegantJointMeasurement.ContinuousCPInstruments.integral_canonicalGram_eq_one _ _
    (P.cpDensity_coordinateMeasurable h) (P.cpDensity_completelyPositive h)
    (P.cpDensity_matrixTraceComplete h)

theorem integrable_canonicalGram (h : H) :
    Integrable (QuantumProver.ElegantJointMeasurement.ContinuousCPInstruments.canonicalGram (P.cpDensity h))
      (P.measureKernel h) :=
  QuantumProver.ElegantJointMeasurement.ContinuousCPInstruments.integrable_canonicalGram _ _
    (P.cpDensity_coordinateMeasurable h) (P.cpDensity_completelyPositive h)
    (P.cpDensity_matrixTraceComplete h)

theorem exists_joint_cp_density :
    ∃ μ : Kernel H Ω, IsMarkovKernel μ ∧
      ∃ Φ : H → Ω → (Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ),
        (∀ i j b c, Measurable
          (fun z : H × Ω => Φ z.1 z.2 (Matrix.single i j 1) b c)) ∧
        (∀ h ω, QuantumProver.ElegantJointMeasurement.CP.CompletelyPositive (Φ h ω)) ∧
        (∀ h, QuantumProver.ElegantJointMeasurement.ContinuousCPInstruments.MatrixTraceComplete (μ h) (Φ h)) ∧
        (∀ h X, Integrable (fun ω => Φ h ω X) (μ h)) ∧
        (∀ h s, MeasurableSet s → ∀ X, (∫ ω in s, Φ h ω X ∂μ h) = P.map h s X) ∧
        (∀ h, ∀ᵐ ω ∂μ h, (QuantumProver.ElegantJointMeasurement.CP.choi (Φ h ω)).trace.re = (Fintype.card I : ℝ)) ∧
        (∀ h, (∫ ω, QuantumProver.ElegantJointMeasurement.ContinuousCPInstruments.canonicalGram (Φ h) ω ∂μ h) = 1) := by
  exact ⟨P.measureKernel, P.measureKernel_isMarkov, P.cpDensity,
    P.cpDensity_joint_coordinate_measurable, P.cpDensity_completelyPositive,
    P.cpDensity_matrixTraceComplete, P.cpDensity_integrable, P.cpDensity_setIntegral,
    P.cpDensity_choi_trace, P.integral_canonicalGram_eq_one⟩

end MatrixCPInstrument

end CP

end QuantumProver.ElegantJointMeasurement.ContinuousInstrumentRadonNikodym
