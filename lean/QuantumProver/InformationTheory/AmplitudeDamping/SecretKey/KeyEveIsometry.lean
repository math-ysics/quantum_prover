import QuantumProver.InformationTheory.AmplitudeDamping.SecretKey.InitialSeedPreparation
import QuantumProver.InformationTheory.AmplitudeDamping.SecretKey.ProtocolReadout

set_option autoImplicit false

noncomputable section

open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix Kronecker

namespace QuantumProver.AmplitudeDamping.SecretKey.KeyEveIsometry

open InitialSeed

section RectangularIsometry

variable {I O : Type*} [Fintype I] [Fintype O] [DecidableEq I] [DecidableEq O]

def isometryDensity (V : Matrix O I ℂ) (hV : Vᴴ * V = 1) (ρ : Density I) :
    Density O where
  mat := V * ρ.mat * Vᴴ
  positive := ρ.positive.mul_mul_conjTranspose_same V
  normalized := (trace_isometry V hV ρ.mat).trans ρ.normalized

theorem sqrt_isometry (V : Matrix O I ℂ) (hV : Vᴴ * V = 1)
    {X : Matrix I I ℂ} (hX : X.PosSemidef) :
    CFC.sqrt (V * X * Vᴴ) = V * CFC.sqrt X * Vᴴ := by
  simpa only [CFC.sqrt_eq_rpow, CFC.rpow_eq_pow] using
    rpow_isometry V hV hX (by norm_num : (1 / 2 : ℝ) ≠ 0)

theorem traceNorm_isometry (V : Matrix O I ℂ) (hV : Vᴴ * V = 1)
    (X : Matrix I I ℂ) : traceNorm (V * X * Vᴴ) = traceNorm X := by
  have hGram : (V * X * Vᴴ)ᴴ * (V * X * Vᴴ) = V * (Xᴴ * X) * Vᴴ := by
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.mul_assoc] using isometry_mul V hV Xᴴ X
  unfold traceNorm CFC.abs
  simp only [Matrix.star_eq_conjTranspose]
  rw [hGram, sqrt_isometry V hV (Matrix.posSemidef_conjTranspose_mul_self X),
    trace_isometry V hV]

theorem rootFidelity_isometry (V : Matrix O I ℂ) (hV : Vᴴ * V = 1)
    (ρ σ : Density I) :
    rootFidelity (isometryDensity V hV ρ) (isometryDensity V hV σ) = rootFidelity ρ σ := by
  unfold rootFidelity
  dsimp only [isometryDensity]
  rw [sqrt_isometry V hV ρ.positive, sqrt_isometry V hV σ.positive,
    isometry_mul V hV, traceNorm_isometry V hV]

theorem squaredFidelity_isometry (V : Matrix O I ℂ) (hV : Vᴴ * V = 1)
    (ρ σ : Density I) :
    squaredFidelity (isometryDensity V hV ρ) (isometryDensity V hV σ) =
      squaredFidelity ρ σ := by
  simp only [squaredFidelity, rootFidelity_isometry]

end RectangularIsometry

section KeyEve

variable {E F : Type*} [Fintype E] [Fintype F] [DecidableEq E] [DecidableEq F]

def keyEveMatrix (d : ℕ) (V : Matrix F E ℂ) :
    Matrix ((Fin d × Fin d) × F) ((Fin d × Fin d) × E) ℂ :=
  (1 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) ⊗ₖ V

theorem keyEveMatrix_isometry (d : ℕ) (V : Matrix F E ℂ) (hV : Vᴴ * V = 1) :
    (keyEveMatrix d V)ᴴ * keyEveMatrix d V = 1 := by
  rw [keyEveMatrix, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
    ← Matrix.mul_kronecker_mul, hV, Matrix.one_mul, Matrix.one_kronecker_one]

theorem idealKeyStateAgainst_isometry (d : ℕ) (hd : 0 < d)
    (V : Matrix F E ℂ) (hV : Vᴴ * V = 1) (ξ : Density E) :
    idealKeyStateAgainst d hd (isometryDensity V hV ξ) =
      isometryDensity (keyEveMatrix d V) (keyEveMatrix_isometry d V hV)
        (idealKeyStateAgainst d hd ξ) := by
  apply Density.eq_of_mat_eq
  change (uniformKeyLaw d hd).copiedMatrix ⊗ₖ (V * ξ.mat * Vᴴ) =
    ((1 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) ⊗ₖ V) *
      ((uniformKeyLaw d hd).copiedMatrix ⊗ₖ ξ.mat) *
      ((1 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) ⊗ₖ V)ᴴ
  rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
    ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    Matrix.one_mul, Matrix.mul_one]

theorem keyG_isometry_le (d : ℕ) (hd : 0 < d)
    (V : Matrix F E ℂ) (hV : Vᴴ * V = 1)
    (ρ : Density ((Fin d × Fin d) × E)) :
    optimalWholeKeySquaredFidelity d hd ρ ≤
      optimalWholeKeySquaredFidelity d hd
        (isometryDensity (keyEveMatrix d V) (keyEveMatrix_isometry d V hV) ρ) := by
  let σ := isometryDensity (keyEveMatrix d V) (keyEveMatrix_isometry d V hV) ρ
  have hTargetBdd : BddAbove (Set.range fun ξ : Density F =>
      squaredFidelity σ (idealKeyStateAgainst d hd ξ)) := by
    refine ⟨1, ?_⟩
    rintro y ⟨ξ, rfl⟩
    exact (MatrixTraceNorm.squaredFidelity_mem_Icc σ _).2
  unfold optimalWholeKeySquaredFidelity
  apply csSup_le
  · exact ⟨_, ⟨ρ.marginalRight, rfl⟩⟩
  · rintro y ⟨ξ, rfl⟩
    have hScore : squaredFidelity σ (idealKeyStateAgainst d hd (isometryDensity V hV ξ)) =
        squaredFidelity ρ (idealKeyStateAgainst d hd ξ) := by
      rw [idealKeyStateAgainst_isometry]
      exact squaredFidelity_isometry _ _ _ _
    exact hScore.symm.le.trans (le_csSup hTargetBdd ⟨isometryDensity V hV ξ, rfl⟩)

theorem keyG_le_of_matrix_isometry (d : ℕ) (hd : 0 < d)
    (V : Matrix F E ℂ) (hV : Vᴴ * V = 1)
    (ρ : Density ((Fin d × Fin d) × E)) (σ : Density ((Fin d × Fin d) × F))
    (hσ : σ.mat = keyEveMatrix d V * ρ.mat * (keyEveMatrix d V)ᴴ) :
    optimalWholeKeySquaredFidelity d hd ρ ≤ optimalWholeKeySquaredFidelity d hd σ := by
  have heq : σ = isometryDensity (keyEveMatrix d V) (keyEveMatrix_isometry d V hV) ρ :=
    Density.eq_of_mat_eq hσ
  rw [heq]
  exact keyG_isometry_le d hd V hV ρ

end KeyEve

section GroundHistory

variable {K H J E : Type*} [Fintype K] [Fintype H] [Fintype J] [Fintype E]
  [DecidableEq K] [DecidableEq H] [DecidableEq J] [DecidableEq E]

theorem basisEmbedding_identity_prod (f : H → J) :
    PublicHistory.basisEmbedding_B (fun x : K × H => (x.1, f x.2)) =
      (1 : Matrix K K ℂ) ⊗ₖ PublicHistory.basisEmbedding_B f := by
  ext x y
  rcases x with ⟨k,h⟩
  rcases y with ⟨k',h'⟩
  by_cases hk : k = k' <;>
    simp [PublicHistory.basisEmbedding_B, Matrix.kronecker_apply, Matrix.one_apply,
      Prod.mk.injEq, hk]

def historyEveEmbedding (f : H → J) : H × E → J × E := fun x => (f x.1, x.2)

theorem historyEveEmbedding_injective (f : H → J) (hf : Function.Injective f) :
    Function.Injective (historyEveEmbedding (E := E) f) := by
  intro x y h
  apply Prod.ext
  · exact hf (congrArg Prod.fst h)
  · exact congrArg (fun t : J × E => t.2) h

theorem keyG_groundHistory_le (d : ℕ) (hd : 0 < d) (f : H → J)
    (hf : Function.Injective f)
    (ρ : Density ((Fin d × Fin d) × (H × E)))
    (σ : Density ((Fin d × Fin d) × (J × E)))
    (hσ : σ.mat =
      PublicHistory.basisEmbedding_B
        (fun x : (Fin d × Fin d) × (H × E) => (x.1, (f x.2.1, x.2.2))) * ρ.mat *
      (PublicHistory.basisEmbedding_B
        (fun x : (Fin d × Fin d) × (H × E) => (x.1, (f x.2.1, x.2.2))))ᴴ) :
    optimalWholeKeySquaredFidelity d hd ρ ≤ optimalWholeKeySquaredFidelity d hd σ := by
  let V := PublicHistory.basisEmbedding_B (historyEveEmbedding (E := E) f)
  have hV : Vᴴ * V = 1 := PublicHistory.basisEmbedding_gram_B _
    (historyEveEmbedding_injective f hf)
  apply keyG_le_of_matrix_isometry d hd V hV ρ σ
  simpa only [keyEveMatrix, V, ← basisEmbedding_identity_prod, historyEveEmbedding] using hσ

end GroundHistory

end QuantumProver.AmplitudeDamping.SecretKey.KeyEveIsometry
