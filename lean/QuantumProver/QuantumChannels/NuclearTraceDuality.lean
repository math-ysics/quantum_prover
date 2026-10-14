import QuantumProver.QuantumChannels.NuclearInstrumentTestIntegral
import QuantumProver.InformationTheory.ElegantJointMeasurement.NormalCompleteContraction

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000

open MeasureTheory InnerProductSpace
open scoped BigOperators InnerProduct ComplexOrder Topology

namespace QuantumProver.MatrixNuclearTraceDuality

open QuantumProver.NuclearOperator QuantumProver.HilbertNuclearCompression
open QuantumProver.MatrixNuclearInstrumentTestIntegral

variable {E F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

private theorem rankOne_add_functional (φ ψ : E →L[ℂ] ℂ) (y : E) :
    rankOne (φ + ψ) y = rankOne φ y + rankOne ψ y := by
  apply toOperator_injective
  ext x
  simp only [map_add, toOperator_rankOne, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smulRight_apply, add_smul]

private theorem rankOne_smul_functional (c : ℂ) (φ : E →L[ℂ] ℂ) (y : E) :
    rankOne (c • φ) y = c • rankOne φ y := by
  apply toOperator_injective
  ext x
  simp only [map_smul, toOperator_rankOne, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, smul_smul, smul_eq_mul]

private theorem rankOne_add_vector (φ : E →L[ℂ] ℂ) (y z : E) :
    rankOne φ (y + z) = rankOne φ y + rankOne φ z := by
  apply toOperator_injective
  ext x
  simp only [map_add, toOperator_rankOne, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smulRight_apply, smul_add]

private theorem rankOne_smul_vector (c : ℂ) (φ : E →L[ℂ] ℂ) (y : E) :
    rankOne φ (c • y) = c • rankOne φ y := by
  apply toOperator_injective
  ext x
  simp only [map_smul, toOperator_rankOne, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, smul_smul, mul_comm]

def pullbackFormLinear (Φ : Nuclear ℂ E E →L[ℂ] Nuclear ℂ F F)
    (W : F →L[ℂ] F) : E →ₗ⋆[ℂ] E →ₗ[ℂ] ℂ where
  toFun y :=
    { toFun := fun x => star (tracePair W (Φ (rankOne (innerSL ℂ x) y)))
      map_add' := by
        intro x z
        simp only [map_add, rankOne_add_functional, tracePair_add, star_add]
      map_smul' := by
        intro c x
        simp only [map_smulₛₗ, rankOne_smul_functional, map_smul,
          tracePair_smul, star_smul, RingHom.id_apply, starRingEnd_apply, star_star] }
  map_add' := by
    intro y z
    ext x
    change star (tracePair W (Φ (rankOne (innerSL ℂ x) (y + z)))) =
      star (tracePair W (Φ (rankOne (innerSL ℂ x) y))) +
        star (tracePair W (Φ (rankOne (innerSL ℂ x) z)))
    simp only [map_add, rankOne_add_vector,
      tracePair_add, star_add]
  map_smul' := by
    intro c y
    ext x
    simp only [LinearMap.smul_apply, rankOne_smul_vector, map_smul,
      tracePair_smul, star_smul]
    rfl

theorem norm_pullbackFormLinear_apply_le
    (Φ : Nuclear ℂ E E →L[ℂ] Nuclear ℂ F F) (W : F →L[ℂ] F) (y x : E) :
    ‖pullbackFormLinear Φ W y x‖ ≤ (‖Φ‖ * ‖W‖) * ‖y‖ * ‖x‖ := by
  change ‖star (tracePair W (Φ (rankOne (innerSL ℂ x) y)))‖ ≤ _
  rw [norm_star]
  calc
    ‖tracePair W (Φ (rankOne (innerSL ℂ x) y))‖
        ≤ ‖W‖ * ‖Φ (rankOne (innerSL ℂ x) y)‖ := norm_tracePair_le _ _
    _ ≤ ‖W‖ * (‖Φ‖ * ‖rankOne (innerSL ℂ x) y‖) :=
      mul_le_mul_of_nonneg_left (Φ.le_opNorm _) (norm_nonneg W)
    _ = (‖Φ‖ * ‖W‖) * ‖y‖ * ‖x‖ := by
      rw [QuantumProver.NuclearOperator.norm_rankOne, innerSL_apply_norm]
      ring

def pullbackForm (Φ : Nuclear ℂ E E →L[ℂ] Nuclear ℂ F F)
    (W : F →L[ℂ] F) : E →L⋆[ℂ] E →L[ℂ] ℂ :=
  (pullbackFormLinear Φ W).mkContinuous₂ (‖Φ‖ * ‖W‖)
    (norm_pullbackFormLinear_apply_le Φ W)

@[simp] theorem pullbackForm_apply
    (Φ : Nuclear ℂ E E →L[ℂ] Nuclear ℂ F F) (W : F →L[ℂ] F) (y x : E) :
    pullbackForm Φ W y x = star (tracePair W (Φ (rankOne (innerSL ℂ x) y))) := rfl

theorem norm_pullbackForm_le (Φ : Nuclear ℂ E E →L[ℂ] Nuclear ℂ F F)
    (W : F →L[ℂ] F) : ‖pullbackForm Φ W‖ ≤ ‖Φ‖ * ‖W‖ :=
  LinearMap.mkContinuous₂_norm_le _ (mul_nonneg (norm_nonneg Φ) (norm_nonneg W)) _

def pullback (Φ : Nuclear ℂ E E →L[ℂ] Nuclear ℂ F F) (W : F →L[ℂ] F) : E →L[ℂ] E :=
  InnerProductSpace.continuousLinearMapOfBilin (pullbackForm Φ W)

theorem inner_pullback (Φ : Nuclear ℂ E E →L[ℂ] Nuclear ℂ F F)
    (W : F →L[ℂ] F) (x y : E) :
    inner ℂ x (pullback Φ W y) = tracePair W (Φ (rankOne (innerSL ℂ x) y)) := by
  rw [← inner_conj_symm]
  simp only [pullback, InnerProductSpace.continuousLinearMapOfBilin_apply,
    pullbackForm_apply, starRingEnd_apply, star_star]

theorem norm_pullback_apply_le (Φ : Nuclear ℂ E E →L[ℂ] Nuclear ℂ F F)
    (W : F →L[ℂ] F) (y : E) : ‖pullback Φ W y‖ ≤ (‖Φ‖ * ‖W‖) * ‖y‖ := by
  calc
    ‖pullback Φ W y‖ = ‖pullbackForm Φ W y‖ :=
      (InnerProductSpace.toDual ℂ E).symm.norm_map _
    _ ≤ ‖pullbackForm Φ W‖ * ‖y‖ := (pullbackForm Φ W).le_opNorm y
    _ ≤ (‖Φ‖ * ‖W‖) * ‖y‖ :=
      mul_le_mul_of_nonneg_right (norm_pullbackForm_le Φ W) (norm_nonneg y)

theorem norm_pullback_le (Φ : Nuclear ℂ E E →L[ℂ] Nuclear ℂ F F)
    (W : F →L[ℂ] F) : ‖pullback Φ W‖ ≤ ‖Φ‖ * ‖W‖ :=
  (pullback Φ W).opNorm_le_bound (by positivity) (norm_pullback_apply_le Φ W)

theorem tracePair_pullback_rankOne (Φ : Nuclear ℂ E E →L[ℂ] Nuclear ℂ F F)
    (W : F →L[ℂ] F) (φ : E →L[ℂ] ℂ) (y : E) :
    tracePair (pullback Φ W) (rankOne φ y) = tracePair W (Φ (rankOne φ y)) := by
  let x := (InnerProductSpace.toDual ℂ E).symm φ
  have hx : innerSL ℂ x = φ := by
    ext z
    exact InnerProductSpace.toDual_symm_apply
  rw [tracePair_rankOne, ← hx]
  exact inner_pullback Φ W x y

theorem tracePair_pullback (Φ : Nuclear ℂ E E →L[ℂ] Nuclear ℂ F F)
    (W : F →L[ℂ] F) (T : Nuclear ℂ E E) :
    tracePair (pullback Φ W) T = tracePair W (Φ T) := by
  obtain ⟨c, rfl⟩ := ofCoefficients_surjective T
  have hleft := (hasSum_ofCoefficients c).mapL (tracePairCLM (pullback Φ W))
  have hright := (hasSum_ofCoefficients c).mapL ((tracePairCLM W).comp Φ)
  have heq : (fun a => tracePairCLM (pullback Φ W) (c a • ofAtom a)) =
      fun a => ((tracePairCLM W).comp Φ) (c a • ofAtom a) := by
    funext a
    simp only [ContinuousLinearMap.comp_apply, map_smul,
      ← rankOne_atom_eq_ofAtom]
    exact congrArg (fun z : ℂ => c a • z)
      (tracePair_pullback_rankOne Φ W a.1.1 a.2.1)
  exact (heq ▸ hleft).unique hright

theorem pullback_unique (Φ : Nuclear ℂ E E →L[ℂ] Nuclear ℂ F F)
    (W : F →L[ℂ] F) (V : E →L[ℂ] E)
    (hV : ∀ T, tracePair V T = tracePair W (Φ T)) : V = pullback Φ W := by
  ext y
  apply ext_inner_left ℂ
  intro x
  rw [inner_pullback, ← hV, tracePair_rankOne]
  rfl

@[simp] theorem pullback_id (W : E →L[ℂ] E) :
    pullback (ContinuousLinearMap.id ℂ (Nuclear ℂ E E)) W = W := by
  symm
  apply pullback_unique
  intro T
  rfl

theorem pullback_comp (Φ : Nuclear ℂ E E →L[ℂ] Nuclear ℂ F F)
    (Ψ : Nuclear ℂ F F →L[ℂ] Nuclear ℂ G G) (W : G →L[ℂ] G) :
    pullback (Ψ.comp Φ) W = pullback Φ (pullback Ψ W) := by
  symm
  apply pullback_unique
  intro T
  rw [tracePair_pullback, tracePair_pullback]
  rfl

@[simp] theorem pullback_zero (Φ : Nuclear ℂ E E →L[ℂ] Nuclear ℂ F F) :
    pullback Φ (0 : F →L[ℂ] F) = 0 := by
  ext y
  apply ext_inner_left ℂ
  intro x
  rw [inner_pullback]
  have hz : compose (0 : F →L[ℂ] F) (ContinuousLinearMap.id ℂ F)
      (Φ (rankOne (innerSL ℂ x) y)) = 0 := by
    apply toOperator_injective
    simp
  simp only [tracePair, tracePairCLM, ContinuousLinearMap.comp_apply, hz,
    map_zero, zero_apply, inner_zero_right]

theorem tracePair_id (T : Nuclear ℂ E E) :
    tracePair (ContinuousLinearMap.id ℂ E) T = QuantumProver.HilbertNuclearTrace.trace T := by
  change QuantumProver.HilbertNuclearTrace.trace (compose (ContinuousLinearMap.id ℂ E)
    (ContinuousLinearMap.id ℂ E) T) = _
  congr 1
  apply toOperator_injective
  simp

theorem trace_nonneg_of_isPositive (T : Nuclear ℂ E E)
    (hT : (toOperator T).IsPositive) : 0 ≤ QuantumProver.HilbertNuclearTrace.trace T := by
  obtain ⟨ι, b, hb⟩ := exists_hilbertBasis ℂ E
  rw [QuantumProver.HilbertNuclearTrace.trace_eq_diagonal_tsum b]
  exact tsum_nonneg (fun i => hT.inner_nonneg_right (b i))

theorem tracePair_nonneg_of_isPositive (W : E →L[ℂ] E) (hW : W.IsPositive)
    (T : Nuclear ℂ E E) (hT : (toOperator T).IsPositive) : 0 ≤ tracePair W T := by
  let S : E →L[ℂ] E := CFC.sqrt W
  have hS : S.IsPositive :=
    ContinuousLinearMap.nonneg_iff_isPositive.mp (CFC.sqrt_nonneg W)
  have hSS : S ∘L S = W := by
    exact CFC.sqrt_mul_sqrt_self W (ContinuousLinearMap.nonneg_iff_isPositive.mpr hW)
  have hSad : S.adjoint = S := hS.isSelfAdjoint.star_eq
  have hpos : (toOperator (compose S S T)).IsPositive := by
    rw [toOperator_compose]
    simpa only [hSad] using hT.adjoint_conj S
  have heq : tracePair W T = QuantumProver.HilbertNuclearTrace.trace (compose S S T) := by
    rw [QuantumProver.ElegantJointMeasurement.NormalCPInstruments.trace_compose_cycle, hSS]
    change QuantumProver.HilbertNuclearTrace.trace (compose W (ContinuousLinearMap.id ℂ E) T) =
      QuantumProver.HilbertNuclearTrace.trace (compose (ContinuousLinearMap.id ℂ E) W T)
    exact QuantumProver.ElegantJointMeasurement.NormalCPInstruments.trace_compose_cycle W
      (ContinuousLinearMap.id ℂ E) T
  rw [heq]
  exact trace_nonneg_of_isPositive _ hpos

theorem pullback_isPositive (Φ : Nuclear ℂ E E →L[ℂ] Nuclear ℂ F F)
    (hCP : QuantumProver.ElegantJointMeasurement.NormalInstrumentAbsorption.NormalCompletelyPositive Φ)
    (W : F →L[ℂ] F) (hW : W.IsPositive) : (pullback Φ W).IsPositive := by
  apply (ContinuousLinearMap.isPositive_iff_complex _).mpr
  intro x
  have hp : 0 ≤ inner ℂ x (pullback Φ W x) := by
    rw [inner_pullback]
    apply tracePair_nonneg_of_isPositive W hW
    apply QuantumProver.ElegantJointMeasurement.NormalCompleteContraction.normalOperation_isPositive Φ hCP
    rw [toOperator_rankOne]
    exact InnerProductSpace.isPositive_rankOne_self x
  have hreal : inner ℂ x (pullback Φ W x) =
      ((inner ℂ x (pullback Φ W x)).re : ℂ) := Complex.eq_re_of_ofReal_le hp
  have hleft : inner ℂ (pullback Φ W x) x =
      ((inner ℂ x (pullback Φ W x)).re : ℂ) := by
    rw [← inner_conj_symm, hreal]
    simp
  rw [hleft]
  exact ⟨rfl, hp.1⟩

theorem pullback_id_of_trace_preserving
    (Φ : Nuclear ℂ E E →L[ℂ] Nuclear ℂ F F)
    (hTP : ∀ T, QuantumProver.HilbertNuclearTrace.trace (Φ T) =
      QuantumProver.HilbertNuclearTrace.trace T) :
    pullback Φ (ContinuousLinearMap.id ℂ F) = ContinuousLinearMap.id ℂ E := by
  ext y
  apply ext_inner_left ℂ
  intro x
  rw [inner_pullback, tracePair_id, hTP, QuantumProver.HilbertNuclearTrace.trace_rankOne]
  rfl

section Histories

variable {H : Type*} [MeasurableSpace H]

theorem measurable_inner_pullback
    (Φ : H → Nuclear ℂ E E →L[ℂ] Nuclear ℂ F F)
    (hΦ : ∀ x y : E, StronglyMeasurable
      (fun h => Φ h (rankOne (innerSL ℂ x) y)))
    (W : H → F →L[ℂ] F)
    (hW : ∀ u v : F, Measurable (fun h => inner ℂ u (W h v)))
    (x y : E) : Measurable (fun h => inner ℂ x (pullback (Φ h) (W h) y)) := by
  simp only [inner_pullback]
  exact (stronglyMeasurable_tracePair W hW (hΦ x y)).measurable

theorem measurable_inner_pullback_of_strong
    (Φ : H → Nuclear ℂ E E →L[ℂ] Nuclear ℂ F F)
    (hΦ : ∀ T, StronglyMeasurable (fun h => Φ h T))
    (W : H → F →L[ℂ] F)
    (hW : ∀ u v : F, Measurable (fun h => inner ℂ u (W h v)))
    (x y : E) : Measurable (fun h => inner ℂ x (pullback (Φ h) (W h) y)) :=
  measurable_inner_pullback Φ (fun x y => hΦ _) W hW x y

theorem weaklyMeasurable_pullback_of_bound
    (Φ : H → Nuclear ℂ E E →L[ℂ] Nuclear ℂ F F)
    (hΦ : ∀ T, StronglyMeasurable (fun h => Φ h T))
    (W : H → F →L[ℂ] F)
    (hW : ∀ u v : F, Measurable (fun h => inner ℂ u (W h v)))
    {C : ℝ} (hbound : ∀ h, ‖W h‖ ≤ C) :
    (∀ x y : E, Measurable (fun h => inner ℂ x (pullback (Φ h) (W h) y))) ∧
      ∀ h, ‖pullback (Φ h) (W h)‖ ≤ ‖Φ h‖ * C := by
  refine ⟨measurable_inner_pullback_of_strong Φ hΦ W hW, ?_⟩
  intro h
  exact (norm_pullback_le (Φ h) (W h)).trans
    (mul_le_mul_of_nonneg_left (hbound h) (norm_nonneg (Φ h)))

end Histories

end QuantumProver.MatrixNuclearTraceDuality
