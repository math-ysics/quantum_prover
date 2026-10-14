import QuantumProver.InformationTheory.AmplitudeDamping.SecretKey.ProtocolReadout
import QuantumProver.InformationTheory.SuperchannelDiscrimination.QuantumTestingPowerBound

set_option autoImplicit false

noncomputable section

open Matrix Filter Topology
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace QuantumProver.AmplitudeDamping.SecretKey.OutputContinuity

open MatrixTraceNorm QuantumProver.MatrixAnalysis.MatrixSqrt

variable {I : Type*} [Fintype I] [DecidableEq I]

@[simp] theorem traceNorm_zero : traceNorm (0 : Matrix I I ℂ) = 0 := by
  simp [traceNorm, CFC.abs_zero]

@[simp] theorem traceNorm_neg (X : Matrix I I ℂ) : traceNorm (-X) = traceNorm X := by
  simp only [traceNorm, CFC.abs_neg]

theorem traceNorm_add_le (X Y : Matrix I I ℂ) :
    traceNorm (X + Y) ≤ traceNorm X + traceNorm Y := by
  obtain ⟨U, hU, hu⟩ := PurificationOrbit.exists_unitary_traceNorm_attainer (X + Y)
  have hx := PurificationOrbit.re_trace_unitary_mul_le_traceNorm X U hU
  have hy := PurificationOrbit.re_trace_unitary_mul_le_traceNorm Y U hU
  rw [Matrix.mul_add, Matrix.trace_add, Complex.add_re] at hu
  linarith

theorem traceNorm_sub_comm (X Y : Matrix I I ℂ) :
    traceNorm (X - Y) = traceNorm (Y - X) := by
  rw [← neg_sub Y X, traceNorm_neg]

theorem traceNorm_sub_le (X Y : Matrix I I ℂ) :
    traceNorm (X - Y) ≤ traceNorm X + traceNorm Y := by
  simpa only [sub_eq_add_neg, traceNorm_neg] using traceNorm_add_le X (-Y)

theorem abs_traceNorm_sub_le (X Y : Matrix I I ℂ) :
    |traceNorm X - traceNorm Y| ≤ traceNorm (X - Y) := by
  have hx := traceNorm_add_le (X - Y) Y
  have hy := traceNorm_add_le (Y - X) X
  rw [sub_add_cancel] at hx hy
  rw [← traceNorm_sub_comm X Y] at hy
  rw [abs_le]
  constructor <;> linarith

theorem hsNorm_sqrt_sub_sq {A B : Matrix I I ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    hsNorm (CFC.sqrt A - CFC.sqrt B) ^ 2 =
      A.trace.re + B.trace.re - 2 * (CFC.sqrt A * CFC.sqrt B).trace.re := by
  have hSA : (CFC.sqrt A)ᴴ = CFC.sqrt A := (CFC.sqrt_nonneg A).posSemidef.isHermitian
  have hSB : (CFC.sqrt B)ᴴ = CFC.sqrt B := (CFC.sqrt_nonneg B).posSemidef.isHermitian
  rw [hsNorm_sq, Matrix.conjTranspose_sub, hSA, hSB]
  simp only [Matrix.sub_mul, Matrix.mul_sub, CFC.sqrt_mul_sqrt_self A hA.nonneg,
    CFC.sqrt_mul_sqrt_self B hB.nonneg, Matrix.trace_sub, Complex.sub_re,
    Matrix.trace_mul_comm (CFC.sqrt B) (CFC.sqrt A)]
  ring

theorem traceNorm_add_trace_sub_eq_twice_posPart {A B : Matrix I I ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    traceNorm (A - B) + A.trace.re - B.trace.re = 2 * (A - B)⁺.trace.re := by
  have h := congrArg (fun X : Matrix I I ℂ => X.trace.re)
    (CFC.abs_add_self (A - B) (hA.sub hB).isSelfAdjoint)
  simp only [two_smul, Matrix.trace_add, Matrix.trace_sub, Complex.add_re,
    Complex.sub_re] at h
  change (CFC.abs (A - B)).trace.re + A.trace.re - B.trace.re = _
  linarith

theorem powers_stormer {A B : Matrix I I ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    hsNorm (CFC.sqrt A - CFC.sqrt B) ^ 2 ≤ traceNorm (A - B) := by
  have hhalf : (1 : ℝ) - 1 / 2 = 1 / 2 := by norm_num
  have ha := QuantumProver.SuperchannelDiscrimination.QuantumTestingPowerBound.audenaert_trace_power
    hA hB (1 / 2) (by norm_num) (by norm_num)
  rw [hhalf, ← CFC.sqrt_eq_rpow, ← CFC.sqrt_eq_rpow] at ha
  rw [hsNorm_sqrt_sub_sq hA hB]
  have ht := traceNorm_add_trace_sub_eq_twice_posPart hA.1 hB.1
  linarith

theorem hsNorm_sqrt_sub_le_sqrt_traceNorm {A B : Matrix I I ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    hsNorm (CFC.sqrt A - CFC.sqrt B) ≤ Real.sqrt (traceNorm (A - B)) := by
  have h := powers_stormer hA hB
  have hn := hsNorm_nonneg (CFC.sqrt A - CFC.sqrt B)
  have ht := traceNorm_nonneg (A - B)
  have hs := Real.sq_sqrt ht
  have hs0 := Real.sqrt_nonneg (traceNorm (A - B))
  nlinarith

theorem abs_rootFidelity_sub_le (ρ τ σ : Density I) :
    |rootFidelity ρ σ - rootFidelity τ σ| ≤ Real.sqrt (traceNorm (ρ.mat - τ.mat)) := by
  have hreverse := abs_traceNorm_sub_le (CFC.sqrt ρ.mat * CFC.sqrt σ.mat)
    (CFC.sqrt τ.mat * CFC.sqrt σ.mat)
  have hholder := traceNorm_mul_le_hs (CFC.sqrt ρ.mat - CFC.sqrt τ.mat) (CFC.sqrt σ.mat)
  rw [hsNorm_sqrt_of_trace_one σ.positive σ.normalized, mul_one] at hholder
  have hps := hsNorm_sqrt_sub_le_sqrt_traceNorm ρ.positive τ.positive
  have hprod : CFC.sqrt ρ.mat * CFC.sqrt σ.mat - CFC.sqrt τ.mat * CFC.sqrt σ.mat =
      (CFC.sqrt ρ.mat - CFC.sqrt τ.mat) * CFC.sqrt σ.mat := (Matrix.sub_mul _ _ _).symm
  rw [hprod] at hreverse
  exact hreverse.trans (hholder.trans hps)

theorem abs_squaredFidelity_sub_le (ρ τ σ : Density I) :
    |squaredFidelity ρ σ - squaredFidelity τ σ| ≤
      2 * Real.sqrt (traceNorm (ρ.mat - τ.mat)) := by
  have hρ := rootFidelity_mem_Icc ρ σ
  have hτ := rootFidelity_mem_Icc τ σ
  have h := abs_rootFidelity_sub_le ρ τ σ
  have hsum : |rootFidelity ρ σ + rootFidelity τ σ| ≤ 2 := by
    rw [abs_of_nonneg (add_nonneg hρ.1 hτ.1)]
    linarith [hρ.2, hτ.2]
  have heq : squaredFidelity ρ σ - squaredFidelity τ σ =
      (rootFidelity ρ σ - rootFidelity τ σ) * (rootFidelity ρ σ + rootFidelity τ σ) := by
    unfold squaredFidelity
    ring
  rw [heq, abs_mul]
  calc
    _ ≤ Real.sqrt (traceNorm (ρ.mat - τ.mat)) * 2 :=
      mul_le_mul h hsum (abs_nonneg _) (Real.sqrt_nonneg _)
    _ = _ := mul_comm _ _

section WholeEve

variable {E : Type*} [Fintype E] [DecidableEq E]

private theorem candidate_bddAbove (d : ℕ) (hd : 0 < d)
    (ρ : Density ((Fin d × Fin d) × E)) :
    BddAbove (Set.range fun ξ : Density E => squaredFidelity ρ (idealKeyStateAgainst d hd ξ)) := by
  refine ⟨1, ?_⟩
  rintro y ⟨ξ, rfl⟩
  exact (squaredFidelity_mem_Icc ρ (idealKeyStateAgainst d hd ξ)).2

theorem squaredFidelity_candidate_le_keyG (d : ℕ) (hd : 0 < d)
    (ρ : Density ((Fin d × Fin d) × E)) (ξ : Density E) :
    squaredFidelity ρ (idealKeyStateAgainst d hd ξ) ≤ optimalWholeKeySquaredFidelity d hd ρ :=
  le_csSup (candidate_bddAbove d hd ρ) ⟨ξ, rfl⟩

theorem keyG_le_add_error (d : ℕ) (hd : 0 < d)
    (ρ τ : Density ((Fin d × Fin d) × E)) :
    optimalWholeKeySquaredFidelity d hd ρ ≤ optimalWholeKeySquaredFidelity d hd τ +
      2 * Real.sqrt (traceNorm (ρ.mat - τ.mat)) := by
  apply csSup_le
  · exact ⟨_, ⟨ρ.marginalRight, rfl⟩⟩
  · rintro y ⟨ξ, rfl⟩
    have h := (abs_le.mp (abs_squaredFidelity_sub_le ρ τ (idealKeyStateAgainst d hd ξ))).2
    have hτ := squaredFidelity_candidate_le_keyG d hd τ ξ
    linarith

theorem abs_keyG_sub_le (d : ℕ) (hd : 0 < d)
    (ρ τ : Density ((Fin d × Fin d) × E)) :
    |optimalWholeKeySquaredFidelity d hd ρ - optimalWholeKeySquaredFidelity d hd τ| ≤
      2 * Real.sqrt (traceNorm (ρ.mat - τ.mat)) := by
  have hρ := keyG_le_add_error d hd ρ τ
  have hτ := keyG_le_add_error d hd τ ρ
  rw [traceNorm_sub_comm τ.mat ρ.mat] at hτ
  rw [abs_le]
  constructor <;> linarith

end WholeEve

section VaryingRegisters

variable {T : Type*} {l : Filter T} {E : T → Type*}
  [∀ t, Fintype (E t)] [∀ t, DecidableEq (E t)]

theorem keyG_difference_tendsto_zero {d : T → ℕ} (hd : ∀ t, 0 < d t)
    (ρ τ : ∀ t, Density ((Fin (d t) × Fin (d t)) × E t))
    (herror : Tendsto (fun t => traceNorm ((ρ t).mat - (τ t).mat)) l (𝓝 0)) :
    Tendsto (fun t => optimalWholeKeySquaredFidelity (d t) (hd t) (ρ t) -
      optimalWholeKeySquaredFidelity (d t) (hd t) (τ t)) l (𝓝 0) := by
  have hs : Tendsto (fun t => 2 * Real.sqrt (traceNorm ((ρ t).mat - (τ t).mat)))
      l (𝓝 0) := by
    simpa only [Function.comp_apply, Real.sqrt_zero, mul_zero] using
      (tendsto_const_nhds (x := (2 : ℝ))).mul (Real.continuous_sqrt.tendsto 0 |>.comp herror)
  exact (tendsto_zero_iff_abs_tendsto_zero _).mpr
    (squeeze_zero (fun t => abs_nonneg _)
      (fun t => abs_keyG_sub_le (d t) (hd t) (ρ t) (τ t)) hs)

theorem keyG_tendsto_of_traceNorm_error {d : T → ℕ} (hd : ∀ t, 0 < d t)
    (ρ τ : ∀ t, Density ((Fin (d t) × Fin (d t)) × E t)) {g : ℝ}
    (herror : Tendsto (fun t => traceNorm ((ρ t).mat - (τ t).mat)) l (𝓝 0))
    (hτ : Tendsto (fun t => optimalWholeKeySquaredFidelity (d t) (hd t) (τ t)) l (𝓝 g)) :
    Tendsto (fun t => optimalWholeKeySquaredFidelity (d t) (hd t) (ρ t)) l (𝓝 g) := by
  have hdiff := keyG_difference_tendsto_zero hd ρ τ herror
  simpa only [sub_add_cancel, zero_add] using hdiff.add hτ

end VaryingRegisters

section WholeEveRelabel

variable {E F : Type*} [Fintype E] [Fintype F] [DecidableEq E] [DecidableEq F]

private theorem relabel_inverse (e : F ≃ E) (ξ : Density F) :
    (ξ.relabel e.symm).relabel e = ξ := by
  apply Density.eq_of_mat_eq
  ext x y
  simp only [Density.relabel, Matrix.submatrix_apply, Equiv.symm_apply_apply]

theorem idealKeyStateAgainst_Eve_relabel (d : ℕ) (hd : 0 < d)
    (e : F ≃ E) (ξ : Density E) :
    (idealKeyStateAgainst d hd ξ).relabel ((Equiv.refl (Fin d × Fin d)).prodCongr e) =
      idealKeyStateAgainst d hd (ξ.relabel e) := by
  apply Density.eq_of_mat_eq
  rfl

theorem candidateFidelity_Eve_relabel (d : ℕ) (hd : 0 < d)
    (e : F ≃ E) (ρ : Density ((Fin d × Fin d) × E)) (ξ : Density E) :
    squaredFidelity (ρ.relabel ((Equiv.refl (Fin d × Fin d)).prodCongr e))
      (idealKeyStateAgainst d hd (ξ.relabel e)) =
      squaredFidelity ρ (idealKeyStateAgainst d hd ξ) := by
  rw [← idealKeyStateAgainst_Eve_relabel d hd e ξ, squaredFidelity_relabel]

theorem keyG_Eve_relabel (d : ℕ) (hd : 0 < d)
    (e : F ≃ E) (ρ : Density ((Fin d × Fin d) × E)) :
    optimalWholeKeySquaredFidelity d hd
      (ρ.relabel ((Equiv.refl (Fin d × Fin d)).prodCongr e)) =
      optimalWholeKeySquaredFidelity d hd ρ := by
  unfold optimalWholeKeySquaredFidelity
  congr 1
  ext y
  constructor
  · rintro ⟨ξ, rfl⟩
    refine ⟨ξ.relabel e.symm, ?_⟩
    have h := candidateFidelity_Eve_relabel d hd e ρ (ξ.relabel e.symm)
    rw [relabel_inverse e ξ] at h
    exact h.symm
  · rintro ⟨ξ, rfl⟩
    exact ⟨ξ.relabel e, candidateFidelity_Eve_relabel d hd e ρ ξ⟩

end WholeEveRelabel

structure FiniteSeedKeyCode (p : ℝ) (m d : ℕ) (k : ℝ) where
  seedSize : ℕ
  aliceAncillaSize : ℕ
  bobAncillaSize : ℕ
  priorEveSize : ℕ
  aliceFinalSize : ℕ
  bobFinalSize : ℕ
  seedLaw : ProbabilityLaw (Fin seedSize)
  aliceAncilla : Density (Fin aliceAncillaSize)
  bobAncilla : Density (Fin bobAncillaSize)
  priorEve : Density (Fin priorEveSize)
  protocol : PhysicalProtocol.FiniteKeyProtocol p
    (seedSize * aliceAncillaSize) (seedSize * bobAncillaSize) aliceFinalSize bobFinalSize
  labelA : Fin aliceFinalSize → Fin d
  labelB : Fin bobFinalSize → Fin d
  calls_le : protocol.calls ≤ m
  seed_alphabet_le : (seedSize : ℝ) ≤ (2 : ℝ) ^ k

namespace FiniteSeedKeyCode

variable {p k : ℝ} {m d : ℕ}

def initialLabEquiv (C : FiniteSeedKeyCode p m d k) :
    (Fin (C.seedSize * C.aliceAncillaSize) × Fin (C.seedSize * C.bobAncillaSize)) ≃
      ((Fin C.seedSize × Fin C.seedSize) × (Fin C.aliceAncillaSize × Fin C.bobAncillaSize)) :=
  ((splitKeyRegister C.seedSize C.aliceAncillaSize).prodCongr
    (splitKeyRegister C.seedSize C.bobAncillaSize)).trans
    (Equiv.prodProdProdComm (Fin C.seedSize) (Fin C.aliceAncillaSize)
      (Fin C.seedSize) (Fin C.bobAncillaSize))

def initialHonest (C : FiniteSeedKeyCode p m d k) :
    Density (Fin (C.seedSize * C.aliceAncillaSize) × Fin (C.seedSize * C.bobAncillaSize)) :=
  (C.seedLaw.copiedDensity.tensor (C.aliceAncilla.tensor C.bobAncilla)).relabel C.initialLabEquiv

def initialDensity (C : FiniteSeedKeyCode p m d k) :
    Density ((Fin (C.seedSize * C.aliceAncillaSize) ×
      Fin (C.seedSize * C.bobAncillaSize)) × Fin C.priorEveSize) :=
  C.initialHonest.tensor C.priorEve

def output (C : FiniteSeedKeyCode p m d k) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    Density ((Fin d × Fin d) × (C.protocol.Environment × Fin C.priorEveSize)) := by
  classical
  exact C.protocol.finalKeyStateWithPriorEveLabels hp0 hp1 C.labelA C.labelB
    (Fin C.priorEveSize) C.initialDensity

end FiniteSeedKeyCode

section OperationalOutputs

variable {p : ℝ} {E : Type*} [Fintype E] [DecidableEq E]

def finiteSeedKeyOutputs (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (m d : ℕ) (k : ℝ) :
    Set (Density ((Fin d × Fin d) × E)) :=
  {ρ | ∃ C : FiniteSeedKeyCode p m d k,
    ∃ e : E ≃ (C.protocol.Environment × Fin C.priorEveSize),
      ρ = (C.output hp0 hp1).relabel ((Equiv.refl (Fin d × Fin d)).prodCongr e)}

def operationalSeedKeyOutputs (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (m d : ℕ) (k : ℝ) :
    Set (Density ((Fin d × Fin d) × E)) :=
  {ρ | ∀ ε : ℝ, 0 < ε → ∃ τ ∈ finiteSeedKeyOutputs hp0 hp1 m d k,
    traceNorm (ρ.mat - τ.mat) < ε}

def strongExponentBound (p z k : ℝ) (m d : ℕ) : ℝ :=
  (2 : ℝ) ^ (-z * (log2 (d : ℝ) - k - (m : ℝ) * channelBz p z))

theorem keyG_le_min_add_uniform_error (d : ℕ) (hd : 0 < d)
    (ρ τ : Density ((Fin d × Fin d) × E)) {ε c : ℝ}
    (herror : traceNorm (ρ.mat - τ.mat) ≤ ε)
    (hfinite : optimalWholeKeySquaredFidelity d hd τ ≤ c) :
    optimalWholeKeySquaredFidelity d hd ρ ≤ min 1 (c + 2 * Real.sqrt ε) := by
  apply le_min (optimalWholeKeySquaredFidelity_mem_Icc d hd ρ).2
  have h := keyG_le_add_error d hd ρ τ
  have hs := Real.sqrt_le_sqrt herror
  linarith

theorem strong_bound_uniform_error (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (m d : ℕ) (hd : 0 < d) (k z : ℝ)
    (hfinite : ∀ C : FiniteSeedKeyCode p m d k,
      optimalWholeKeySquaredFidelity d hd (C.output hp0 hp1) ≤ strongExponentBound p z k m d)
    (ρ τ : Density ((Fin d × Fin d) × E))
    (hτ : τ ∈ finiteSeedKeyOutputs hp0 hp1 m d k) {ε : ℝ}
    (herror : traceNorm (ρ.mat - τ.mat) ≤ ε) :
    optimalWholeKeySquaredFidelity d hd ρ ≤
      min 1 (strongExponentBound p z k m d + 2 * Real.sqrt ε) := by
  rcases hτ with ⟨C, e, rfl⟩
  apply keyG_le_min_add_uniform_error d hd ρ _ herror
  rw [keyG_Eve_relabel d hd e]
  exact hfinite C

theorem keyG_le_of_operationalApproximation {d : ℕ} (hd : 0 < d)
    (S : Set (Density ((Fin d × Fin d) × E))) {c : ℝ}
    (hfinite : ∀ τ ∈ S, optimalWholeKeySquaredFidelity d hd τ ≤ c)
    (ρ : Density ((Fin d × Fin d) × E))
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ τ ∈ S, traceNorm (ρ.mat - τ.mat) < ε) :
    optimalWholeKeySquaredFidelity d hd ρ ≤ c := by
  by_contra hn
  have hgap : 0 < optimalWholeKeySquaredFidelity d hd ρ - c := sub_pos.mpr (lt_of_not_ge hn)
  let a := (optimalWholeKeySquaredFidelity d hd ρ - c) / 4
  have ha : 0 < a := div_pos hgap (by norm_num)
  obtain ⟨τ, hτ, herr⟩ := happrox (a ^ 2) (sq_pos_of_pos ha)
  have ht := traceNorm_nonneg (ρ.mat - τ.mat)
  have hs0 := Real.sqrt_nonneg (traceNorm (ρ.mat - τ.mat))
  have hs2 := Real.sq_sqrt ht
  have hs : Real.sqrt (traceNorm (ρ.mat - τ.mat)) < a := by nlinarith
  have hG := keyG_le_add_error d hd ρ τ
  have hτG := hfinite τ hτ
  dsimp only [a] at hs
  linarith

theorem strong_bound_on_operationalOutputs (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (m d : ℕ) (hd : 0 < d) (k z : ℝ)
    (hfinite : ∀ C : FiniteSeedKeyCode p m d k,
      optimalWholeKeySquaredFidelity d hd (C.output hp0 hp1) ≤ strongExponentBound p z k m d)
    (ρ : Density ((Fin d × Fin d) × E))
    (hρ : ρ ∈ operationalSeedKeyOutputs hp0 hp1 m d k) :
    optimalWholeKeySquaredFidelity d hd ρ ≤ min 1 (strongExponentBound p z k m d) := by
  apply le_min (optimalWholeKeySquaredFidelity_mem_Icc d hd ρ).2
  apply keyG_le_of_operationalApproximation hd (finiteSeedKeyOutputs hp0 hp1 m d k) _ ρ hρ
  rintro τ ⟨C, e, rfl⟩
  rw [keyG_Eve_relabel d hd e]
  exact hfinite C

end OperationalOutputs

end QuantumProver.AmplitudeDamping.SecretKey.OutputContinuity
