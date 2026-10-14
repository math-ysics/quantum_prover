import QuantumProver.InformationTheory.MeasuredRelativeEntropyVariational

set_option autoImplicit false

noncomputable section

open Filter Set Topology
open scoped BigOperators ComplexOrder MatrixOrder Matrix Matrix.Norms.L2Operator
open QuantumProver.SuperchannelDiscrimination.FlaggedStates
open QuantumProver.MeasuredRelativeEntropyVariational

namespace QuantumProver.MeasuredRelativeEntropyContinuity

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem continuous_matrixObjectiveBits (Omega : Mat I) :
    Continuous (fun p : Mat I × Mat I => matrixObjectiveBits p.1 p.2 Omega) := by
  unfold matrixObjectiveBits
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  fun_prop

theorem continuous_matrixObjectiveBits_ereal (Omega : Mat I) :
    Continuous (fun p : Mat I × Mat I => (matrixObjectiveBits p.1 p.2 Omega : EReal)) :=
  continuous_coe_real_ereal.comp (continuous_matrixObjectiveBits Omega)

theorem variationalRelativeEntropyBits_eq_iSup (rho sigma : Mat I) :
    variationalRelativeEntropyBits rho sigma =
      ⨆ Omega : {X : Mat I // X.PosDef}, (matrixObjectiveBits rho sigma Omega.val : EReal) := by
  have heq : matrixVariationalValues rho sigma =
      Set.range (fun Omega : {X : Mat I // X.PosDef} =>
        (matrixObjectiveBits rho sigma Omega.val : EReal)) := by
    ext z
    constructor
    · rintro ⟨Omega, hOmega, hz⟩
      exact ⟨⟨Omega, hOmega⟩, hz.symm⟩
    · rintro ⟨Omega, hz⟩
      exact ⟨Omega.val, Omega.prop, hz.symm⟩
  rw [variationalRelativeEntropyBits, heq, sSup_range]

theorem lowerSemicontinuous_variationalRelativeEntropyBits :
    LowerSemicontinuous (fun p : Mat I × Mat I =>
      variationalRelativeEntropyBits p.1 p.2) := by
  simp_rw [variationalRelativeEntropyBits_eq_iSup]
  exact lowerSemicontinuous_iSup (fun Omega =>
    (continuous_matrixObjectiveBits_ereal Omega.val).lowerSemicontinuous)

theorem lowerSemicontinuousOn_measuredRelativeEntropyBits :
    LowerSemicontinuousOn (fun p : Mat I × Mat I => measuredRelativeEntropyBits p.1 p.2)
      {p | IsDensity p.1 ∧ p.2.PosSemidef} := by
  intro p hp z hz
  have hpEq : measuredRelativeEntropyBits p.1 p.2 =
      variationalRelativeEntropyBits p.1 p.2 :=
    measuredRelativeEntropyBits_variational p.1 p.2 hp.1 hp.2
  have hz' : z < variationalRelativeEntropyBits p.1 p.2 := hpEq ▸ hz
  have hv := (lowerSemicontinuous_variationalRelativeEntropyBits (I := I)).lowerSemicontinuousWithinAt
    {p : Mat I × Mat I | IsDensity p.1 ∧ p.2.PosSemidef} p
  filter_upwards [hv z hz', self_mem_nhdsWithin] with q hq hqS
  have hqEq : measuredRelativeEntropyBits q.1 q.2 =
      variationalRelativeEntropyBits q.1 q.2 :=
    measuredRelativeEntropyBits_variational q.1 q.2 hqS.1 hqS.2
  exact hqEq.symm ▸ hq

theorem measuredRelativeEntropyBits_le_liminf
    {α : Type*} {l : Filter α} [NeBot l]
    {rho sigma : Mat I} {rhoSeq sigmaSeq : α → Mat I}
    (hRho : IsDensity rho) (hSigma : sigma.PosSemidef)
    (hRhoSeq : ∀ a, IsDensity (rhoSeq a))
    (hSigmaSeq : ∀ a, (sigmaSeq a).PosSemidef)
    (hRhoLim : Tendsto rhoSeq l (𝓝 rho))
    (hSigmaLim : Tendsto sigmaSeq l (𝓝 sigma)) :
    measuredRelativeEntropyBits rho sigma ≤
      Filter.liminf (fun a => measuredRelativeEntropyBits (rhoSeq a) (sigmaSeq a)) l := by
  let S : Set (Mat I × Mat I) := {p | IsDensity p.1 ∧ p.2.PosSemidef}
  let f : Mat I × Mat I → EReal := fun p => measuredRelativeEntropyBits p.1 p.2
  let v : α → Mat I × Mat I := fun a => (rhoSeq a, sigmaSeq a)
  have hv : Tendsto v l (𝓝[S] (rho, sigma)) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact ⟨hRhoLim.prodMk_nhds hSigmaLim,
      Filter.Eventually.of_forall (fun a => ⟨hRhoSeq a, hSigmaSeq a⟩)⟩
  have hsc : LowerSemicontinuousWithinAt f S (rho, sigma) :=
    lowerSemicontinuousOn_measuredRelativeEntropyBits (I := I) (rho, sigma) ⟨hRho, hSigma⟩
  have hf : f (rho, sigma) ≤ Filter.liminf f (𝓝[S] (rho, sigma)) :=
    LowerSemicontinuousWithinAt.le_liminf hsc
  exact hf.trans hv.liminf_le_liminf_comp

theorem measuredRelativeEntropyBits_le_liminf_atTop
    {rho sigma : Mat I} {rhoSeq sigmaSeq : ℕ → Mat I}
    (hRho : IsDensity rho) (hSigma : sigma.PosSemidef)
    (hRhoSeq : ∀ n, IsDensity (rhoSeq n))
    (hSigmaSeq : ∀ n, (sigmaSeq n).PosSemidef)
    (hRhoLim : Tendsto rhoSeq atTop (𝓝 rho))
    (hSigmaLim : Tendsto sigmaSeq atTop (𝓝 sigma)) :
    measuredRelativeEntropyBits rho sigma ≤
      Filter.liminf (fun n => measuredRelativeEntropyBits (rhoSeq n) (sigmaSeq n)) atTop :=
  measuredRelativeEntropyBits_le_liminf hRho hSigma hRhoSeq hSigmaSeq hRhoLim hSigmaLim

end QuantumProver.MeasuredRelativeEntropyContinuity
