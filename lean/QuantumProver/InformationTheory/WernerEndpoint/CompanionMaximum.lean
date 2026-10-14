import QuantumProver.InformationTheory.WernerEndpoint.AntisymmetricStates

set_option autoImplicit false

noncomputable section

namespace QuantumProver.WernerEndpoint.CompanionMaximum

open scoped BigOperators Topology

variable {Y B : Type*} [Fintype Y] [Fintype B] [DecidableEq Y]

def pureOutputPurityRange (Phi : Matrix Y Y ℂ →ₗ[ℂ] Matrix B B ℂ) : Set ℝ :=
  {p | ∃ v : Y → ℂ, vectorNormSq v = 1 ∧ purity (Phi (pureDensity v)) = p}

def pureOutputPurityMaximum (Phi : Matrix Y Y ℂ →ₗ[ℂ] Matrix B B ℂ) : ℝ :=
  sSup (pureOutputPurityRange Phi)

omit [DecidableEq Y] in
theorem vectorNormSq_ofLp (v : EuclideanSpace ℂ Y) :
    vectorNormSq (WithLp.ofLp v) = ‖v‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [vectorNormSq, Complex.sq_norm]

omit [DecidableEq Y] in
theorem continuous_pureOutputPurity (Phi : Matrix Y Y ℂ →ₗ[ℂ] Matrix B B ℂ) :
    Continuous (fun v : EuclideanSpace ℂ Y => purity (Phi (pureDensity (WithLp.ofLp v)))) := by
  have hp : Continuous (fun v : EuclideanSpace ℂ Y => pureDensity (WithLp.ofLp v)) := by
    apply continuous_matrix
    intro i j
    simp only [pureDensity, crossDensity]
    fun_prop
  have hm := Phi.continuous_of_finiteDimensional.comp hp
  exact Complex.continuous_re.comp ((hm.matrix_mul hm).matrix_trace)

theorem unitSphere_nonempty [Nonempty Y] :
    (Metric.sphere (0 : EuclideanSpace ℂ Y) 1).Nonempty := by
  classical
  let y : Y := Classical.choice inferInstance
  let v : EuclideanSpace ℂ Y := PiLp.single 2 y (1 : ℂ)
  have hn : ‖v‖ = 1 := by simp [v]
  exact ⟨v, by simpa using hn⟩

theorem exists_pureOutputPurity_maximizer [Nonempty Y]
    (Phi : Matrix Y Y ℂ →ₗ[ℂ] Matrix B B ℂ) :
    ∃ v : Y → ℂ, vectorNormSq v = 1 ∧
      ∀ w : Y → ℂ, vectorNormSq w = 1 →
        purity (Phi (pureDensity w)) ≤ purity (Phi (pureDensity v)) := by
  obtain ⟨v, hv, hmax⟩ :=
    (isCompact_sphere (0 : EuclideanSpace ℂ Y) 1).exists_isMaxOn unitSphere_nonempty
      (continuous_pureOutputPurity Phi).continuousOn
  have hn : ‖v‖ = 1 := by simpa using hv
  refine ⟨WithLp.ofLp v, ?_, ?_⟩
  · rw [vectorNormSq_ofLp, hn]
    norm_num
  · intro w hw
    let u : EuclideanSpace ℂ Y := WithLp.toLp 2 w
    have hs : ‖u‖ ^ 2 = 1 := by
      rw [← vectorNormSq_ofLp]
      exact hw
    have hu : ‖u‖ = 1 := by nlinarith [norm_nonneg u]
    exact hmax (by simpa using hu)

theorem pureOutputPurityRange_nonempty [Nonempty Y]
    (Phi : Matrix Y Y ℂ →ₗ[ℂ] Matrix B B ℂ) : (pureOutputPurityRange Phi).Nonempty := by
  obtain ⟨v, hv, hmax⟩ := exists_pureOutputPurity_maximizer Phi
  exact ⟨purity (Phi (pureDensity v)), v, hv, rfl⟩

theorem pureOutputPurityRange_bddAbove [Nonempty Y]
    (Phi : Matrix Y Y ℂ →ₗ[ℂ] Matrix B B ℂ) : BddAbove (pureOutputPurityRange Phi) := by
  obtain ⟨v, hv, hmax⟩ := exists_pureOutputPurity_maximizer Phi
  refine ⟨purity (Phi (pureDensity v)), ?_⟩
  rintro p ⟨w, hw, rfl⟩
  exact hmax w hw

theorem pureOutputPurity_le_maximum [Nonempty Y]
    (Phi : Matrix Y Y ℂ →ₗ[ℂ] Matrix B B ℂ)
    (v : Y → ℂ) (hv : vectorNormSq v = 1) :
    purity (Phi (pureDensity v)) ≤ pureOutputPurityMaximum Phi :=
  le_csSup (pureOutputPurityRange_bddAbove Phi) ⟨v, hv, rfl⟩

theorem exists_pureOutputPurity_eq_maximum [Nonempty Y]
    (Phi : Matrix Y Y ℂ →ₗ[ℂ] Matrix B B ℂ) :
    ∃ v : Y → ℂ, vectorNormSq v = 1 ∧
      purity (Phi (pureDensity v)) = pureOutputPurityMaximum Phi := by
  obtain ⟨v, hv, hmax⟩ := exists_pureOutputPurity_maximizer Phi
  refine ⟨v, hv, le_antisymm (pureOutputPurity_le_maximum Phi v hv) ?_⟩
  apply csSup_le (pureOutputPurityRange_nonempty Phi)
  rintro p ⟨w, hw, rfl⟩
  exact hmax w hw

end QuantumProver.WernerEndpoint.CompanionMaximum
