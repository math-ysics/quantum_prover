import QuantumProver.InformationTheory.AmplitudeDamping.SecretKey.ProtocolReadout
import QuantumProver.InformationTheory.AmplitudeDamping.SecretKey.PurificationBounds

noncomputable section

open scoped BigOperators Topology ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace QuantumProver.AmplitudeDamping.SecretKey.SemanticVerification

theorem withPriorEve_preserves_prior_Eve
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {a b af bf : ℕ}
    (P : PhysicalProtocol.FiniteKeyProtocol p a b af bf)
    (E : Type*) [Fintype E]
    (ρ : Matrix ((Fin a × Fin b) × E) ((Fin a × Fin b) × E) ℂ) :
    partialTraceLeft (P.withPriorEve E ρ) = partialTraceLeft ρ := by
  ext e e'
  change (∑ o : (Fin af × Fin bf) × P.Environment,
    P.fullOutput (Matrix.of (fun i j => ρ (i, e) (j, e'))) o o) =
      ∑ i : Fin a × Fin b, ρ (i, e) (i, e')
  simpa only [Matrix.trace, Matrix.diag, Matrix.of_apply] using
    P.fullOutput_trace hp0 hp1 (Matrix.of (fun i j => ρ (i, e) (j, e')))

theorem onDensityWithPriorEve_preserves_prior_Eve
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {a b af bf : ℕ}
    (P : PhysicalProtocol.FiniteKeyProtocol p a b af bf)
    (E : Type*) [Fintype E] [DecidableEq E]
    (ρ : Density ((Fin a × Fin b) × E)) :
    (P.onDensityWithPriorEve hp0 hp1 E ρ).marginalRight.mat =
      ρ.marginalRight.mat := by
  exact withPriorEve_preserves_prior_Eve hp0 hp1 P E ρ.mat

theorem onDensityWholeEve_preserves_prior_Eve
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {a b af bf : ℕ}
    (P : PhysicalProtocol.FiniteKeyProtocol p a b af bf)
    (E : Type*) [Fintype E] [DecidableEq E]
    (ρ : Density ((Fin a × Fin b) × E)) :
    partialTraceLeft (P.onDensityWholeEve hp0 hp1 E ρ).marginalRight.mat =
      ρ.marginalRight.mat := by
  ext e e'
  change (∑ l : P.Environment, ∑ o : Fin af × Fin bf,
    P.fullOutput (Matrix.of (fun i j => ρ.mat (i, e) (j, e'))) (o, l) (o, l)) =
      ∑ i : Fin a × Fin b, ρ.mat (i, e) (i, e')
  rw [Finset.sum_comm]
  simpa only [Matrix.trace, Matrix.diag, Fintype.sum_prod_type,
    Matrix.of_apply] using
      P.fullOutput_trace hp0 hp1 (Matrix.of (fun i j => ρ.mat (i, e) (j, e')))

theorem finalKeyStateWithPriorEveLabels_isCCQ
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {a b d af bf : ℕ}
    (P : PhysicalProtocol.FiniteKeyProtocol p a b af bf)
    (labelA : Fin af → Fin d) (labelB : Fin bf → Fin d)
    (E : Type*) [Fintype E] [DecidableEq E]
    (ρ : Density ((Fin a × Fin b) × E)) :
    IsCCQ (P.finalKeyStateWithPriorEveLabels hp0 hp1 labelA labelB E ρ) := by
  classical
  exact privateLabelReadout_isCCQ
    (fun i : Fin af × Fin bf => (labelA i.1, labelB i.2))
    (P.onDensityWholeEve hp0 hp1 E ρ)

theorem finalKeyStateWithPriorEveLabels_preserves_whole_Eve
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {a b d af bf : ℕ}
    (P : PhysicalProtocol.FiniteKeyProtocol p a b af bf)
    (labelA : Fin af → Fin d) (labelB : Fin bf → Fin d)
    (E : Type*) [Fintype E] [DecidableEq E]
    (ρ : Density ((Fin a × Fin b) × E)) :
    (P.finalKeyStateWithPriorEveLabels hp0 hp1 labelA labelB E ρ).marginalRight.mat =
      (P.onDensityWholeEve hp0 hp1 E ρ).marginalRight.mat := by
  classical
  exact privateLabelReadout_preserves_Eve
    (fun i : Fin af × Fin bf => (labelA i.1, labelB i.2))
    (P.onDensityWholeEve hp0 hp1 E ρ)

theorem finalKeyStateWithPriorEveLabels_preserves_prior_Eve
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {a b d af bf : ℕ}
    (P : PhysicalProtocol.FiniteKeyProtocol p a b af bf)
    (labelA : Fin af → Fin d) (labelB : Fin bf → Fin d)
    (E : Type*) [Fintype E] [DecidableEq E]
    (ρ : Density ((Fin a × Fin b) × E)) :
    partialTraceLeft
      (P.finalKeyStateWithPriorEveLabels hp0 hp1 labelA labelB E ρ).marginalRight.mat =
        ρ.marginalRight.mat := by
  rw [finalKeyStateWithPriorEveLabels_preserves_whole_Eve]
  exact onDensityWholeEve_preserves_prior_Eve hp0 hp1 P E ρ

theorem finalKeyStateWithPriorEve_isCCQ
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {a b d af bf : ℕ}
    (P : PhysicalProtocol.FiniteKeyProtocol p a b (d * af) (d * bf))
    (E : Type*) [Fintype E] [DecidableEq E]
    (ρ : Density ((Fin a × Fin b) × E)) :
    IsCCQ (P.finalKeyStateWithPriorEve hp0 hp1 E ρ) := by
  classical
  exact privateKeyReadout_isCCQ d af bf (P.onDensityWholeEve hp0 hp1 E ρ)

theorem finalKeyStateWithPriorEve_preserves_whole_Eve
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {a b d af bf : ℕ}
    (P : PhysicalProtocol.FiniteKeyProtocol p a b (d * af) (d * bf))
    (E : Type*) [Fintype E] [DecidableEq E]
    (ρ : Density ((Fin a × Fin b) × E)) :
    (P.finalKeyStateWithPriorEve hp0 hp1 E ρ).marginalRight.mat =
      (P.onDensityWholeEve hp0 hp1 E ρ).marginalRight.mat := by
  classical
  exact privateKeyReadout_preserves_Eve d af bf (P.onDensityWholeEve hp0 hp1 E ρ)

end QuantumProver.AmplitudeDamping.SecretKey.SemanticVerification

namespace QuantumProver.AmplitudeDamping.SecretKey.SemanticVerification

theorem finalKeyStateWithPriorEveLabels_squaredFidelity_directSum
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {a b d af bf : ℕ} (hd : 0 < d)
    (P : PhysicalProtocol.FiniteKeyProtocol p a b af bf) [DecidableEq P.Environment]
    (labelA : Fin af → Fin d) (labelB : Fin bf → Fin d)
    (E : Type*) [Fintype E] [DecidableEq E]
    (ρ : Density ((Fin a × Fin b) × E)) (ξ : Density (P.Environment × E)) :
    squaredFidelity (P.finalKeyStateWithPriorEveLabels hp0 hp1 labelA labelB E ρ)
      (idealKeyStateAgainst d hd ξ) =
      (1 / (d : ℝ)) * (∑ i : Fin d,
        traceNorm (CFC.sqrt (classicalKeyBlock
          (P.finalKeyStateWithPriorEveLabels hp0 hp1 labelA labelB E ρ) (i, i)) *
            CFC.sqrt ξ.mat)) ^ 2 := by
  exact squaredFidelity_isCCQ_ideal_directSum d hd _
    (finalKeyStateWithPriorEveLabels_isCCQ hp0 hp1 P labelA labelB E ρ) ξ

theorem finalKeyStateWithPriorEveLabels_optimalFidelity_directSum
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {a b d af bf : ℕ} (hd : 0 < d)
    (P : PhysicalProtocol.FiniteKeyProtocol p a b af bf) [DecidableEq P.Environment]
    (labelA : Fin af → Fin d) (labelB : Fin bf → Fin d)
    (E : Type*) [Fintype E] [DecidableEq E]
    (ρ : Density ((Fin a × Fin b) × E)) :
    optimalWholeKeySquaredFidelity d hd
      (P.finalKeyStateWithPriorEveLabels hp0 hp1 labelA labelB E ρ) =
      sSup (Set.range fun ξ : Density (P.Environment × E) =>
        (1 / (d : ℝ)) * (∑ i : Fin d,
          traceNorm (CFC.sqrt (classicalKeyBlock
            (P.finalKeyStateWithPriorEveLabels hp0 hp1 labelA labelB E ρ) (i, i)) *
              CFC.sqrt ξ.mat)) ^ 2) := by
  unfold optimalWholeKeySquaredFidelity
  congr 2
  funext ξ
  exact finalKeyStateWithPriorEveLabels_squaredFidelity_directSum
    hp0 hp1 hd P labelA labelB E ρ ξ

theorem finalKeyStateWithPriorEveLabels_blocks_sum_whole_Eve
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {a b d af bf : ℕ}
    (P : PhysicalProtocol.FiniteKeyProtocol p a b af bf)
    (labelA : Fin af → Fin d) (labelB : Fin bf → Fin d)
    (E : Type*) [Fintype E] [DecidableEq E]
    (ρ : Density ((Fin a × Fin b) × E)) :
    (∑ k : Fin d × Fin d, classicalKeyBlock
      (P.finalKeyStateWithPriorEveLabels hp0 hp1 labelA labelB E ρ) k) =
      (P.onDensityWholeEve hp0 hp1 E ρ).marginalRight.mat := by
  rw [sum_classicalKeyBlock_eq_marginalRight,
    finalKeyStateWithPriorEveLabels_preserves_whole_Eve]

theorem finalKeyStateWithPriorEveLabels_optimalFidelity_mem_Icc
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {a b d af bf : ℕ} (hd : 0 < d)
    (P : PhysicalProtocol.FiniteKeyProtocol p a b af bf) [DecidableEq P.Environment]
    (labelA : Fin af → Fin d) (labelB : Fin bf → Fin d)
    (E : Type*) [Fintype E] [DecidableEq E]
    (ρ : Density ((Fin a × Fin b) × E)) :
    optimalWholeKeySquaredFidelity d hd
      (P.finalKeyStateWithPriorEveLabels hp0 hp1 labelA labelB E ρ) ∈ Set.Icc (0 : ℝ) 1 := by
  exact MatrixTraceNorm.optimalWholeKeySquaredFidelity_mem_Icc d hd _

end QuantumProver.AmplitudeDamping.SecretKey.SemanticVerification

namespace QuantumProver.AmplitudeDamping.SecretKey.SemanticVerification

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem continuous_traceNorm_matrix : Continuous (traceNorm : Matrix I I ℂ → ℝ) := by
  have hTrace : Continuous (fun M : Matrix I I ℂ => M.trace.re) := by
    simp only [Matrix.trace, Matrix.diag]
    fun_prop
  exact hTrace.comp CFC.continuous_abs

theorem continuousOn_rootFidelity_matrix :
    ContinuousOn (fun x : Matrix I I ℂ × Matrix I I ℂ =>
      traceNorm (CFC.sqrt x.1 * CFC.sqrt x.2))
      {x | x.1.PosSemidef ∧ x.2.PosSemidef} := by
  have hRoot : ContinuousOn (CFC.sqrt : Matrix I I ℂ → Matrix I I ℂ)
      {M | M.PosSemidef} := by
    simpa only [Matrix.nonneg_iff_posSemidef] using
      (CFC.continuousOn_sqrt (A := Matrix I I ℂ))
  have hLeft : ContinuousOn
      (fun x : Matrix I I ℂ × Matrix I I ℂ => CFC.sqrt x.1)
      {x | x.1.PosSemidef ∧ x.2.PosSemidef} :=
    hRoot.comp continuous_fst.continuousOn (fun _ hx => hx.1)
  have hRight : ContinuousOn
      (fun x : Matrix I I ℂ × Matrix I I ℂ => CFC.sqrt x.2)
      {x | x.1.PosSemidef ∧ x.2.PosSemidef} :=
    hRoot.comp continuous_snd.continuousOn (fun _ hx => hx.2)
  exact continuous_traceNorm_matrix.comp_continuousOn (hLeft.mul hRight)

theorem continuousOn_squaredFidelity_matrix :
    ContinuousOn (fun x : Matrix I I ℂ × Matrix I I ℂ =>
      (traceNorm (CFC.sqrt x.1 * CFC.sqrt x.2)) ^ 2)
      {x | x.1.PosSemidef ∧ x.2.PosSemidef} :=
  continuousOn_rootFidelity_matrix.pow 2

theorem tendsto_squaredFidelity_of_matrix_tendsto
    {T : Type*} {l : Filter T} (ρ : T → Density I) (ρ₀ σ : Density I)
    (hρ : Filter.Tendsto (fun t => (ρ t).mat) l (𝓝 ρ₀.mat)) :
    Filter.Tendsto (fun t => squaredFidelity (ρ t) σ) l
      (𝓝 (squaredFidelity ρ₀ σ)) := by
  have hPair : Filter.Tendsto (fun t => ((ρ t).mat, σ.mat)) l
      (𝓝 (ρ₀.mat, σ.mat)) := hρ.prodMk_nhds tendsto_const_nhds
  have hWithin : Filter.Tendsto (fun t => ((ρ t).mat, σ.mat)) l
      (𝓝[{x : Matrix I I ℂ × Matrix I I ℂ | x.1.PosSemidef ∧ x.2.PosSemidef}]
        (ρ₀.mat, σ.mat)) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨hPair, Filter.Eventually.of_forall fun t => ⟨(ρ t).positive, σ.positive⟩⟩
  have hc := continuousOn_squaredFidelity_matrix (ρ₀.mat, σ.mat)
    ⟨ρ₀.positive, σ.positive⟩
  simpa only [squaredFidelity, rootFidelity, Function.comp_def] using hc.tendsto.comp hWithin

theorem optimalFidelity_bound_passes_to_fixed_matrix_limit
    {T E : Type*} [Fintype E] [DecidableEq E]
    {l : Filter T} [l.NeBot] (d : ℕ) (hd : 0 < d)
    (ρ : T → Density ((Fin d × Fin d) × E))
    (ρ₀ : Density ((Fin d × Fin d) × E)) (B : ℝ)
    (hρ : Filter.Tendsto (fun t => (ρ t).mat) l (𝓝 ρ₀.mat))
    (hBound : ∀ t, optimalWholeKeySquaredFidelity d hd (ρ t) ≤ B) :
    optimalWholeKeySquaredFidelity d hd ρ₀ ≤ B := by
  have hBdd (t : T) : BddAbove (Set.range fun ξ : Density E =>
      squaredFidelity (ρ t) (idealKeyStateAgainst d hd ξ)) := by
    refine ⟨1, ?_⟩
    rintro y ⟨ξ, rfl⟩
    exact (MatrixTraceNorm.squaredFidelity_mem_Icc _ _).2
  change sSup (Set.range fun ξ : Density E =>
    squaredFidelity ρ₀ (idealKeyStateAgainst d hd ξ)) ≤ B
  have hNonempty : (Set.range fun ξ : Density E =>
      squaredFidelity ρ₀ (idealKeyStateAgainst d hd ξ)).Nonempty :=
    ⟨squaredFidelity ρ₀ (idealKeyStateAgainst d hd ρ₀.marginalRight),
      ⟨ρ₀.marginalRight, rfl⟩⟩
  apply csSup_le hNonempty
  rintro y ⟨ξ, rfl⟩
  have hCandidate (t : T) :
      squaredFidelity (ρ t) (idealKeyStateAgainst d hd ξ) ≤ B :=
    (le_csSup (hBdd t) ⟨ξ, rfl⟩).trans (hBound t)
  exact le_of_tendsto
    (tendsto_squaredFidelity_of_matrix_tendsto ρ ρ₀ (idealKeyStateAgainst d hd ξ) hρ)
    (Filter.Eventually.of_forall hCandidate)

end QuantumProver.AmplitudeDamping.SecretKey.SemanticVerification
