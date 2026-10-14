import QuantumProver.InformationTheory.SuperchannelDiscrimination.ChannelUniformApproximation
import QuantumProver.InformationTheory.SuperchannelDiscrimination.PetzSmoothing

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Matrix Kronecker

namespace QuantumProver.SuperchannelDiscrimination.ChannelUniformTensorTransport

open Matrix TensorWordTruncation ChannelUniformApproximation WeakRateReduction

def regroup (A B C D : Type*) : ((A × B) × (C × D)) ≃ ((A × C) × (B × D)) where
  toFun x := ((x.1.1, x.2.1), (x.1.2, x.2.2))
  invFun x := ((x.1.1, x.2.1), (x.1.2, x.2.2))
  left_inv x := by rcases x with ⟨⟨a, b⟩, ⟨c, d⟩⟩; rfl
  right_inv x := by rcases x with ⟨⟨a, b⟩, ⟨c, d⟩⟩; rfl

def productStack {I₀ I₁ O₀ O₁ F₀ F₁ : Type*}
    (B₀ : Matrix (O₀ × F₀) I₀ ℂ) (B₁ : Matrix (O₁ × F₁) I₁ ℂ) :
    Matrix ((O₀ × O₁) × (F₀ × F₁)) (I₀ × I₁) ℂ :=
  (B₀ ⊗ₖ B₁).submatrix (regroup O₀ O₁ F₀ F₁) (Equiv.refl (I₀ × I₁))

theorem action_reindex {I O E F I' O' E' F' : Type*}
    [Fintype F] [Fintype F']
    (B : Matrix (O × F) I ℂ) (C : Matrix E F ℂ)
    (eI : I' ≃ I) (eO : O' ≃ O) (eE : E' ≃ E) (eF : F' ≃ F) :
    action (B.submatrix (Equiv.prodCongr eO eF) eI) (C.submatrix eE eF) =
      (action B C).submatrix (Equiv.prodCongr eO eE) eI := by
  ext ⟨o, e⟩ i
  change (∑ f' : F', C (eE e) (eF f') * B (eO o, eF f') (eI i)) =
    ∑ f : F, C (eE e) f * B (eO o, f) (eI i)
  exact Fintype.sum_equiv eF _ _ (fun _ => rfl)

theorem action_productStack {I₀ I₁ O₀ O₁ E₀ E₁ F₀ F₁ : Type*}
    [Fintype F₀] [Fintype F₁]
    (B₀ : Matrix (O₀ × F₀) I₀ ℂ) (B₁ : Matrix (O₁ × F₁) I₁ ℂ)
    (C₀ : Matrix E₀ F₀ ℂ) (C₁ : Matrix E₁ F₁ ℂ) :
    action (productStack B₀ B₁) (C₀ ⊗ₖ C₁) =
      productStack (action B₀ C₀) (action B₁ C₁) := by
  ext ⟨⟨o₀, o₁⟩, ⟨e₀, e₁⟩⟩ ⟨i₀, i₁⟩
  simp only [action, productStack, Matrix.submatrix_apply, Matrix.kroneckerMap_apply,
    regroup, Equiv.coe_fn_mk, Equiv.refl_apply, Fintype.sum_prod_type,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro f₀ _
  apply Finset.sum_congr rfl
  intro f₁ _
  ring

theorem norm_submatrix_difference_equiv {I J I' J' : Type*}
    [Fintype I] [Fintype J] [Fintype I'] [Fintype J']
    [DecidableEq I] [DecidableEq J] [DecidableEq I'] [DecidableEq J']
    (A B : Matrix I J ℂ) (e : I' ≃ I) (f : J' ≃ J) :
    ‖A.submatrix e f - B.submatrix e f‖ = ‖A - B‖ := by
  have h : A.submatrix e f - B.submatrix e f = (A - B).submatrix e f := rfl
  rw [h]
  exact norm_submatrix_equiv _ _ _

theorem rowsBlockPaddingEquiv_pair {O E : Type*} (k m h : ℕ)
    (o : Fin (k * m + h) → O) (e : Fin (k * m + h) → E) :
    rowsBlockPaddingEquiv (O × E) k m h (fun a => (o a, e a)) =
      (fun a b => ((rowsBlockPaddingEquiv O k m h o).1 a b,
        (rowsBlockPaddingEquiv E k m h e).1 a b),
       fun a => ((rowsBlockPaddingEquiv O k m h o).2 a,
        (rowsBlockPaddingEquiv E k m h e).2 a)) := rfl

theorem rowsIntegerPaddingEquiv_pair {O E : Type*} (N : ℕ)
    (o : Fin N → O) (e : Fin N → E) :
    rowsIntegerPaddingEquiv (O × E) N (fun a => (o a, e a)) =
      (fun a b => ((rowsIntegerPaddingEquiv O N o).1 a b,
        (rowsIntegerPaddingEquiv E N e).1 a b),
       fun a => ((rowsIntegerPaddingEquiv O N o).2 a,
        (rowsIntegerPaddingEquiv E N e).2 a)) := rfl

def blockStackRowsEquiv (O E : Type*) (k m h : ℕ) :
    ((Fin (k * m + h) → O) × (Fin (k * m + h) → E)) ≃
      (((Fin k → Fin m → O) × (Fin k → Fin m → E)) ×
        ((Fin h → O) × (Fin h → E))) :=
  (Equiv.prodCongr (rowsBlockPaddingEquiv O k m h)
    (rowsBlockPaddingEquiv E k m h)).trans
      (regroup (Fin k → Fin m → O) (Fin h → O)
        (Fin k → Fin m → E) (Fin h → E))

def integerStackRowsEquiv (O E : Type*) (N : ℕ) :
    ((Fin N → O) × (Fin N → E)) ≃
      (((Fin (blockCount N) → Fin (blockSize N) → O) ×
        (Fin (blockCount N) → Fin (blockSize N) → E)) ×
        ((Fin (paddingSize N) → O) × (Fin (paddingSize N) → E))) :=
  (Equiv.prodCongr (rowsIntegerPaddingEquiv O N)
    (rowsIntegerPaddingEquiv E N)).trans
      (regroup (Fin (blockCount N) → Fin (blockSize N) → O) (Fin (paddingSize N) → O)
        (Fin (blockCount N) → Fin (blockSize N) → E) (Fin (paddingSize N) → E))

variable {I O E F : Type*} [Fintype I] [Fintype O] [Fintype E] [Fintype F]
  [DecidableEq I] [DecidableEq O] [DecidableEq E] [DecidableEq F]

theorem tensorStack_block_padding (B : F → Matrix O I ℂ) (k m h : ℕ) :
    stackKraus (tensorKraus B (k * m + h)) =
      (stackKraus (tensorKraus (tensorKraus B m) k) ⊗ₖ stackKraus (tensorKraus B h)).submatrix
        (blockStackRowsEquiv O F k m h) (rowsBlockPaddingEquiv I k m h) := by
  ext ⟨o, f⟩ i
  have ht := congrArg (fun M :
      Matrix ((Fin k → Fin m → O × F) × (Fin h → O × F))
        ((Fin k → Fin m → I) × (Fin h → I)) ℂ =>
      M (rowsBlockPaddingEquiv (O × F) k m h (fun a => (o a, f a)))
        (rowsBlockPaddingEquiv I k m h i))
    (tensorMatrix_const_block_padding_submatrix (stackKraus B) k m h)
  simp only [Matrix.submatrix_apply, Equiv.symm_apply_apply] at ht
  rw [rowsBlockPaddingEquiv_pair] at ht
  simpa only [stackKraus, tensorKraus, tensorMatrix, blockStackRowsEquiv,
    Matrix.submatrix_apply, Matrix.kroneckerMap_apply, Equiv.coe_trans,
    Equiv.prodCongr_apply, regroup, Equiv.coe_fn_mk, Function.comp_apply, Prod.map_apply] using ht

theorem tensorStack_integer_padding (B : F → Matrix O I ℂ) (N : ℕ) :
    stackKraus (tensorKraus B N) =
      (stackKraus (tensorKraus (tensorKraus B (blockSize N)) (blockCount N)) ⊗ₖ
        stackKraus (tensorKraus B (paddingSize N))).submatrix
          (integerStackRowsEquiv O F N) (rowsIntegerPaddingEquiv I N) := by
  ext ⟨o, f⟩ i
  have ht := congrArg (fun M :
      Matrix ((Fin (blockCount N) → Fin (blockSize N) → O × F) × (Fin (paddingSize N) → O × F))
        ((Fin (blockCount N) → Fin (blockSize N) → I) × (Fin (paddingSize N) → I)) ℂ =>
      M (rowsIntegerPaddingEquiv (O × F) N (fun a => (o a, f a)))
        (rowsIntegerPaddingEquiv I N i))
    (tensorMatrix_const_integer_padding_submatrix (stackKraus B) N)
  simp only [Matrix.submatrix_apply, Equiv.symm_apply_apply] at ht
  rw [rowsIntegerPaddingEquiv_pair] at ht
  simpa only [stackKraus, tensorKraus, tensorMatrix, integerStackRowsEquiv,
    Matrix.submatrix_apply, Matrix.kroneckerMap_apply, Equiv.coe_trans,
    Equiv.prodCongr_apply, regroup, Equiv.coe_fn_mk, Function.comp_apply, Prod.map_apply] using ht

def blockPaddedCoefficient (k m h : ℕ)
    (Db : Matrix (Fin k → Fin m → E) (Fin k → Fin m → F) ℂ)
    (Dp : Matrix (Fin h → E) (Fin h → F) ℂ) :
    Matrix (Fin (k * m + h) → E) (Fin (k * m + h) → F) ℂ :=
  (Db ⊗ₖ Dp).submatrix (rowsBlockPaddingEquiv E k m h) (rowsBlockPaddingEquiv F k m h)

def integerPaddedCoefficient (N : ℕ)
    (Db : Matrix (Fin (blockCount N) → Fin (blockSize N) → E)
      (Fin (blockCount N) → Fin (blockSize N) → F) ℂ)
    (Dp : Matrix (Fin (paddingSize N) → E) (Fin (paddingSize N) → F) ℂ) :
    Matrix (Fin N → E) (Fin N → F) ℂ :=
  (Db ⊗ₖ Dp).submatrix (rowsIntegerPaddingEquiv E N) (rowsIntegerPaddingEquiv F N)

theorem blockPaddedCoefficient_norm_le (k m h : ℕ)
    (Db : Matrix (Fin k → Fin m → E) (Fin k → Fin m → F) ℂ)
    (Dp : Matrix (Fin h → E) (Fin h → F) ℂ) :
    ‖blockPaddedCoefficient k m h Db Dp‖ ≤ ‖Db‖ * ‖Dp‖ := by
  rw [blockPaddedCoefficient, norm_submatrix_equiv]
  exact norm_kronecker_le _ _

theorem integerPaddedCoefficient_norm_le (N : ℕ)
    (Db : Matrix (Fin (blockCount N) → Fin (blockSize N) → E)
      (Fin (blockCount N) → Fin (blockSize N) → F) ℂ)
    (Dp : Matrix (Fin (paddingSize N) → E) (Fin (paddingSize N) → F) ℂ) :
    ‖integerPaddedCoefficient N Db Dp‖ ≤ ‖Db‖ * ‖Dp‖ := by
  rw [integerPaddedCoefficient, norm_submatrix_equiv]
  exact norm_kronecker_le _ _

theorem blockPaddedCoefficient_stack (B : F → Matrix O I ℂ) (k m h : ℕ)
    (Db : Matrix (Fin k → Fin m → E) (Fin k → Fin m → F) ℂ)
    (Dp : Matrix (Fin h → E) (Fin h → F) ℂ) :
    stackKraus (mixEnvironment (blockPaddedCoefficient k m h Db Dp) (tensorKraus B (k * m + h))) =
      (stackKraus (mixEnvironment Db (tensorKraus (tensorKraus B m) k)) ⊗ₖ
        stackKraus (mixEnvironment Dp (tensorKraus B h))).submatrix
          (blockStackRowsEquiv O E k m h) (rowsBlockPaddingEquiv I k m h) := by
  simp only [stackKraus_mixEnvironment_action]
  rw [tensorStack_block_padding]
  change action ((productStack (stackKraus (tensorKraus (tensorKraus B m) k))
    (stackKraus (tensorKraus B h))).submatrix
      (Equiv.prodCongr (rowsBlockPaddingEquiv O k m h) (rowsBlockPaddingEquiv F k m h))
      (rowsBlockPaddingEquiv I k m h))
    ((Db ⊗ₖ Dp).submatrix (rowsBlockPaddingEquiv E k m h) (rowsBlockPaddingEquiv F k m h)) = _
  rw [action_reindex, action_productStack]
  rfl

theorem integerPaddedCoefficient_stack (B : F → Matrix O I ℂ) (N : ℕ)
    (Db : Matrix (Fin (blockCount N) → Fin (blockSize N) → E)
      (Fin (blockCount N) → Fin (blockSize N) → F) ℂ)
    (Dp : Matrix (Fin (paddingSize N) → E) (Fin (paddingSize N) → F) ℂ) :
    stackKraus (mixEnvironment (integerPaddedCoefficient N Db Dp) (tensorKraus B N)) =
      (stackKraus (mixEnvironment Db (tensorKraus (tensorKraus B (blockSize N)) (blockCount N))) ⊗ₖ
        stackKraus (mixEnvironment Dp (tensorKraus B (paddingSize N)))).submatrix
          (integerStackRowsEquiv O E N) (rowsIntegerPaddingEquiv I N) := by
  simp only [stackKraus_mixEnvironment_action]
  rw [tensorStack_integer_padding]
  change action ((productStack (stackKraus (tensorKraus (tensorKraus B (blockSize N)) (blockCount N)))
    (stackKraus (tensorKraus B (paddingSize N)))).submatrix
      (Equiv.prodCongr (rowsIntegerPaddingEquiv O N) (rowsIntegerPaddingEquiv F N))
      (rowsIntegerPaddingEquiv I N))
    ((Db ⊗ₖ Dp).submatrix (rowsIntegerPaddingEquiv E N) (rowsIntegerPaddingEquiv F N)) = _
  rw [action_reindex, action_productStack]
  rfl

theorem exact_padding_mix (K : E → Matrix O I ℂ) (B : F → Matrix O I ℂ)
    (Cstar : Matrix E F ℂ) (hCstar : mixEnvironment Cstar B = K) (h : ℕ) :
    mixEnvironment (tensorMatrix (fun _ : Fin h => Cstar)) (tensorKraus B h) =
      tensorKraus K h := by
  rw [← tensorKraus_mixEnvironment, hCstar]

theorem tensorStack_mixed_difference_norm_eq (K : E → Matrix O I ℂ)
    (B : F → Matrix O I ℂ) (k : ℕ)
    (D : Matrix (Fin k → E) (Fin k → F) ℂ) :
    ‖stackKraus (mixEnvironment D (tensorKraus B k)) - stackKraus (tensorKraus K k)‖ =
      ‖tensorAction (stackKraus B) D - tensorMatrix (fun _ : Fin k => stackKraus K)‖ := by
  rw [stackKraus_tensor_environment_action, stackKraus_tensorKraus,
    norm_submatrix_difference_equiv]

theorem blockPaddedCoefficient_residual_norm_le (K : E → Matrix O I ℂ)
    (B : F → Matrix O I ℂ) (Cstar : Matrix E F ℂ) (hCstar : mixEnvironment Cstar B = K)
    (k m h : ℕ) (Db : Matrix (Fin k → Fin m → E) (Fin k → Fin m → F) ℂ)
    (hpad : ‖stackKraus (tensorKraus K h)‖ ≤ 1) :
    ‖stackKraus (mixEnvironment
        (blockPaddedCoefficient k m h Db (tensorMatrix (fun _ : Fin h => Cstar)))
        (tensorKraus B (k * m + h))) - stackKraus (tensorKraus K (k * m + h))‖ ≤
      ‖stackKraus (mixEnvironment Db (tensorKraus (tensorKraus B m) k)) -
        stackKraus (tensorKraus (tensorKraus K m) k)‖ := by
  rw [blockPaddedCoefficient_stack, exact_padding_mix K B Cstar hCstar h,
    tensorStack_block_padding K k m h, norm_submatrix_difference_equiv]
  exact kronecker_padding_difference_norm_le _ _ _ hpad

theorem integerPaddedCoefficient_residual_norm_le (K : E → Matrix O I ℂ)
    (B : F → Matrix O I ℂ) (Cstar : Matrix E F ℂ) (hCstar : mixEnvironment Cstar B = K)
    (N : ℕ) (Db : Matrix (Fin (blockCount N) → Fin (blockSize N) → E)
      (Fin (blockCount N) → Fin (blockSize N) → F) ℂ)
    (hpad : ‖stackKraus (tensorKraus K (paddingSize N))‖ ≤ 1) :
    ‖stackKraus (mixEnvironment
        (integerPaddedCoefficient N Db (tensorMatrix (fun _ : Fin (paddingSize N) => Cstar)))
        (tensorKraus B N)) - stackKraus (tensorKraus K N)‖ ≤
      ‖stackKraus (mixEnvironment Db (tensorKraus (tensorKraus B (blockSize N)) (blockCount N))) -
        stackKraus (tensorKraus (tensorKraus K (blockSize N)) (blockCount N))‖ := by
  rw [integerPaddedCoefficient_stack, exact_padding_mix K B Cstar hCstar (paddingSize N),
    tensorStack_integer_padding K N, norm_submatrix_difference_equiv]
  exact kronecker_padding_difference_norm_le _ _ _ hpad

end QuantumProver.SuperchannelDiscrimination.ChannelUniformTensorTransport
