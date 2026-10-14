import QuantumProver.QuantumGates.ControlledCliffordHierarchy.HierarchyBounds

noncomputable section

open scoped Matrix BigOperators

namespace QuantumProver.ControlledCliffordHierarchy

theorem conjugate_adjoint {n : ℕ} (U P : QuantumMatrix n) :
    conjugate U P.conjTranspose = (conjugate U P).conjTranspose := by
  simp only [conjugate, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, mul_assoc]

theorem unitary_push_right {n : ℕ} {U : QuantumMatrix n}
    (hU : unitaryMatrix U) (P : QuantumMatrix n) :
    U * P = conjugate U P * U := by
  symm
  calc
    conjugate U P * U = U * P * (U.conjTranspose * U) := by
      simp only [conjugate, mul_assoc]
    _ = U * P := by rw [hU.1, mul_one]

def branchProfileStep {n : ℕ} (U V P : QuantumMatrix n) : QuantumMatrix n :=
  U * P * V.conjTranspose * P.conjTranspose

theorem branchProfileStep_dressed {n : ℕ} {F H : QuantumMatrix n}
    (hF : unitaryMatrix F) (hH : unitaryMatrix H)
    (Y W P : QuantumMatrix n) (a b : ℂ) :
    branchProfileStep (a • (Y * F)) (b • (W * H)) P =
      (a * star b) •
        (Y * conjugate F P *
          (conjugate (F * H.conjTranspose) W).conjTranspose *
          (conjugate (F * H.conjTranspose) P).conjTranspose *
          (F * H.conjTranspose)) := by
  let G : QuantumMatrix n := F * H.conjTranspose
  have hG : unitaryMatrix G :=
    unitaryMatrix_mul hF (unitaryMatrix_conjTranspose hH)
  have hGW : G * W.conjTranspose = (conjugate G W).conjTranspose * G := by
    rw [← conjugate_adjoint]
    exact unitary_push_right hG _
  have hGP : G * P.conjTranspose = (conjugate G P).conjTranspose * G := by
    rw [← conjugate_adjoint]
    exact unitary_push_right hG _
  have hword : branchProfileStep (Y * F) (W * H) P =
      Y * conjugate F P * (conjugate G W).conjTranspose *
        (conjugate G P).conjTranspose * G := by
    simp only [branchProfileStep, Matrix.conjTranspose_mul]
    calc
      Y * F * P * (H.conjTranspose * W.conjTranspose) * P.conjTranspose =
          Y * (F * P) * H.conjTranspose * W.conjTranspose * P.conjTranspose := by
        simp only [mul_assoc]
      _ = Y * conjugate F P * G * W.conjTranspose * P.conjTranspose := by
        rw [unitary_push_right hF P]
        simp only [G, mul_assoc]
      _ = Y * conjugate F P * (G * W.conjTranspose) * P.conjTranspose := by
        simp only [mul_assoc]
      _ = Y * conjugate F P * (conjugate G W).conjTranspose *
          (G * P.conjTranspose) := by
        rw [hGW]
        simp only [mul_assoc]
      _ = Y * conjugate F P * (conjugate G W).conjTranspose *
          (conjugate G P).conjTranspose * G := by
        rw [hGP]
        simp only [mul_assoc]
  simpa only [branchProfileStep, Matrix.conjTranspose_smul,
    smul_mul_assoc, mul_smul_comm, smul_smul, G,
    show star b * a = a * star b from mul_comm _ _] using
    congrArg (fun M : QuantumMatrix n => (a * star b) • M) hword

theorem orderedPauli_four_mul {n : ℕ}
    (xy zy xf zf xg zg xh zh : BitString n) :
    orderedPauli xy zy * orderedPauli xf zf *
      orderedPauli xg zg * orderedPauli xh zh =
        bitSign (dot zy xf + dot (zy + zf) xg + dot (zy + zf + zg) xh) •
          orderedPauli (xy + xf + xg + xh) (zy + zf + zg + zh) := by
  simp only [orderedPauli_mul, smul_mul_assoc, smul_smul, character,
    ← bitSign_add]

theorem branchProfileStep_signed_ordered {n : ℕ} {F H : QuantumMatrix n}
    (hF : unitaryMatrix F) (hH : unitaryMatrix H)
    (xy zy xw zw xp zp xf zf xg zg xh zh : BitString n)
    (tf tw tp : ZMod 2) (a b : ℂ)
    (hf : conjugate F (orderedPauli xp zp) = bitSign tf • orderedPauli xf zf)
    (hw : conjugate (F * H.conjTranspose) (orderedPauli xw zw) =
      bitSign tw • orderedPauli xg zg)
    (hp : conjugate (F * H.conjTranspose) (orderedPauli xp zp) =
      bitSign tp • orderedPauli xh zh) :
    branchProfileStep (a • (orderedPauli xy zy * F))
        (b • (orderedPauli xw zw * H)) (orderedPauli xp zp) =
      (a * star b * bitSign
        (tf + tw + tp + dot zg xg + dot zh xh +
          (dot zy xf + dot (zy + zf) xg + dot (zy + zf + zg) xh))) •
        (orderedPauli (xy + xf + xg + xh) (zy + zf + zg + zh) *
          (F * H.conjTranspose)) := by
  rw [branchProfileStep_dressed hF hH, hf, hw, hp]
  simp only [Matrix.conjTranspose_smul, bitSign_star, orderedPauli_conjTranspose,
    character, smul_mul_assoc, mul_smul_comm, smul_smul]
  rw [orderedPauli_four_mul]
  simp only [smul_mul_assoc, smul_smul, bitSign_add]
  congr 1
  ring

end QuantumProver.ControlledCliffordHierarchy

open scoped Matrix BigOperators

namespace QuantumProver.ControlledCliffordHierarchy

def controlQuad {V : Type*} [AddCommGroup V] (y : ZMod 2 → ZMod 2 → V) : V :=
  y 0 0 + y 0 1 + y 1 0 + y 1 1

theorem controlQuad_add {V : Type*} [AddCommGroup V]
    (y w : ZMod 2 → ZMod 2 → V) :
    controlQuad (fun c b => y c b + w c b) = controlQuad y + controlQuad w := by
  simp only [controlQuad]
  abel

theorem controlQuad_translate {V : Type*} [AddCommGroup V]
    (y : ZMod 2 → ZMod 2 → V) (ac ab : ZMod 2) :
    controlQuad (fun c b => y (c + ac) (b + ab)) = controlQuad y := by
  rcases physical_control_bit_cases ac with rfl | rfl <;>
    rcases physical_control_bit_cases ab with rfl | rfl <;>
    simp only [controlQuad, add_zero, zero_add,
      show (1 + 1 : ZMod 2) = 0 by decide] <;>
    abel

theorem module_charTwo_add_self {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (v : V) : v + v = 0 := by
  rw [← two_smul (ZMod 2) v, show (2 : ZMod 2) = 0 by decide, zero_smul]

theorem controlQuad_const {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (v : V) : controlQuad (fun _ _ : ZMod 2 => v) = 0 := by
  simp only [controlQuad, module_charTwo_add_self, zero_add]

theorem controlQuad_linearMap {V W : Type*} [AddCommGroup V] [AddCommGroup W]
    [Module (ZMod 2) V] [Module (ZMod 2) W]
    (L : V →ₗ[ZMod 2] W) (y : ZMod 2 → ZMod 2 → V) :
    controlQuad (fun c b => L (y c b)) = L (controlQuad y) := by
  simp only [controlQuad, map_add]

theorem controlQuad_mem {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (W : Submodule (ZMod 2) V) (y : ZMod 2 → ZMod 2 → V)
    (hy : ∀ c b, y c b ∈ W) : controlQuad y ∈ W :=
  W.add_mem (W.add_mem (W.add_mem (hy 0 0) (hy 0 1)) (hy 1 0)) (hy 1 1)

def labelProfileStep {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (y : ZMod 2 → ZMod 2 → V)
    (F G : ZMod 2 → ZMod 2 → V →ₗ[ZMod 2] V)
    (ac ab : ZMod 2) (z : V) : ZMod 2 → ZMod 2 → V :=
  fun c b => y c b + G c b (y (c + ac) (b + ab)) + F c b z + G c b z

theorem controlQuad_variable_action {V : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] (y : ZMod 2 → ZMod 2 → V)
    (G : ZMod 2 → ZMod 2 → V →ₗ[ZMod 2] V) (G0 : V →ₗ[ZMod 2] V)
    (ac ab : ZMod 2) :
    controlQuad (fun c b => G c b (y (c + ac) (b + ab))) =
      G0 (controlQuad y) +
        controlQuad (fun c b => (G c b - G0) (y (c + ac) (b + ab))) := by
  have hsplit :
      controlQuad (fun c b => G c b (y (c + ac) (b + ab))) =
        G0 (controlQuad (fun c b => y (c + ac) (b + ab))) +
          controlQuad (fun c b => (G c b - G0) (y (c + ac) (b + ab))) := by
    simp only [controlQuad, map_add, LinearMap.sub_apply]
    abel
  rw [hsplit, controlQuad_translate]

theorem controlQuad_labelProfileStep {V : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] (y : ZMod 2 → ZMod 2 → V)
    (F G : ZMod 2 → ZMod 2 → V →ₗ[ZMod 2] V) (G0 : V →ₗ[ZMod 2] V)
    (ac ab : ZMod 2) (z : V) :
    controlQuad (labelProfileStep y F G ac ab z) =
      (controlQuad y + G0 (controlQuad y)) +
        controlQuad (fun c b => (G c b - G0) (y (c + ac) (b + ab))) +
        controlQuad (fun c b => F c b z) + controlQuad (fun c b => G c b z) := by
  have he : controlQuad (labelProfileStep y F G ac ab z) =
      controlQuad y + controlQuad (fun c b => G c b (y (c + ac) (b + ab))) +
        controlQuad (fun c b => F c b z) + controlQuad (fun c b => G c b z) := by
    unfold controlQuad labelProfileStep
    abel
  rw [he, controlQuad_variable_action y G G0 ac ab]
  abel

theorem labelProfileStep_quad_mem {V : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] (W Wnext : Submodule (ZMod 2) V)
    (y : ZMod 2 → ZMod 2 → V)
    (F G : ZMod 2 → ZMod 2 → V →ₗ[ZMod 2] V) (G0 : V →ₗ[ZMod 2] V)
    (hy : controlQuad y ∈ W)
    (hG0 : ∀ v ∈ W, v + G0 v ∈ Wnext)
    (hDelta : ∀ c b v, (G c b - G0) v ∈ Wnext)
    (hF : ∀ z, controlQuad (fun c b => F c b z) ∈ Wnext)
    (ac ab : ZMod 2) (z : V) :
    controlQuad (labelProfileStep y F G ac ab z) ∈ Wnext := by
  have hG : controlQuad (fun c b => G c b z) ∈ Wnext := by
    have heq : (fun c b => G c b z) =
        (fun c b => G0 z + (G c b - G0) z) := by
      funext c b
      simp only [LinearMap.sub_apply]
      abel
    rw [heq, controlQuad_add, controlQuad_const, zero_add]
    exact controlQuad_mem Wnext _ (fun c b => hDelta c b z)
  rw [controlQuad_labelProfileStep y F G G0 ac ab z]
  exact Wnext.add_mem (Wnext.add_mem (Wnext.add_mem (hG0 _ hy)
    (controlQuad_mem Wnext _ (fun c b => hDelta c b _))) (hF z)) hG

theorem labelProfileStep_quad_zero {V : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] (y : ZMod 2 → ZMod 2 → V)
    (F : ZMod 2 → ZMod 2 → V →ₗ[ZMod 2] V) (G0 : V →ₗ[ZMod 2] V)
    (hY : controlQuad y + G0 (controlQuad y) = 0)
    (hF : ∀ z, controlQuad (fun c b => F c b z) = 0)
    (ac ab : ZMod 2) (z : V) :
    controlQuad (labelProfileStep y F (fun _ _ => G0) ac ab z) = 0 := by
  rw [controlQuad_labelProfileStep y F (fun _ _ => G0) G0 ac ab z]
  simp only [sub_self, LinearMap.zero_apply, controlQuad_const, hY, hF,
    add_zero]

def signedOrderedPauli {n : ℕ} (s : ZMod 2) (p : PauliLabel n) : QuantumMatrix n :=
  bitSign s • orderedPauli p.1 p.2

theorem signedOrderedPauli_actual {n : ℕ} (s : ZMod 2) (p : PauliLabel n) :
    actualPauli (signedOrderedPauli s p) :=
  actualPauli_smul (bitSign_phase s) (orderedPauli_actual p.1 p.2)

theorem signedOrderedPauli_mul {n : ℕ} (s t : ZMod 2) (p q : PauliLabel n) :
    signedOrderedPauli s p * signedOrderedPauli t q =
      signedOrderedPauli (s + t + dot p.2 q.1) (p + q) := by
  simp only [signedOrderedPauli, smul_mul_assoc, mul_smul_comm, smul_smul,
    orderedPauli_mul, character, bitSign_add, mul_assoc]
  congr 1
  ring

theorem signedOrderedPauli_adjoint {n : ℕ} (s : ZMod 2) (p : PauliLabel n) :
    (signedOrderedPauli s p).conjTranspose =
      signedOrderedPauli (s + dot p.2 p.1) p := by
  simp only [signedOrderedPauli, Matrix.conjTranspose_smul, bitSign_star,
    orderedPauli_conjTranspose, character, smul_smul, bitSign_add]

theorem signedOrderedPauli_same_label_branch {n : ℕ} (s t : ZMod 2)
    (p : PauliLabel n) :
    actualPauli (branchMatrix (signedOrderedPauli s p) (signedOrderedPauli t p)) := by
  have h := actualPauli_smul (bitSign_phase s)
    (actualPauli_branch_sign (orderedPauli_actual p.1 p.2) (s + t))
  have heq : bitSign s * bitSign (s + t) = bitSign t := by
    rw [bitSign_add, ← mul_assoc, bitSign_mul_self, one_mul]
  simpa only [← branchMatrix_smul, smul_smul, heq, signedOrderedPauli] using h

theorem hierarchy_branch_of_clifford_pauli_ratio {n : ℕ} {B A : QuantumMatrix n}
    (hB : hierarchy n 2 B) (hBA : actualPauli (B.conjTranspose * A)) :
    hierarchy (n + 1) 2 (branchMatrix B A) := by
  rw [branchMatrix_clifford_factor hB.1]
  exact hierarchy_clifford_mul_left (by omega) (hierarchy_lift (by omega) hB)
    (controlled_actualPauli_clifford hBA)

theorem branch_actualPaulis_clifford {n : ℕ} {B A : QuantumMatrix n}
    (hB : actualPauli B) (hA : actualPauli A) :
    hierarchy (n + 1) 2 (branchMatrix B A) :=
  hierarchy_branch_of_clifford_pauli_ratio
    (actualPauli_hierarchy (by omega) hB)
    (actualPauli_mul (actualPauli_conjTranspose hB) hA)

theorem twoControlMatrix_signed_affine_clifford {n : ℕ}
    (s : ZMod 2 → ZMod 2 → ZMod 2) (y : ZMod 2 → ZMod 2 → PauliLabel n)
    (hy : controlQuad y = 0) :
    hierarchy ((n + 1) + 1) 2
      (twoControlMatrix (fun c b => signedOrderedPauli (s c b) (y c b))) := by
  have hsum : (y 0 0 + y 1 0) + (y 0 1 + y 1 1) = 0 := by
    simpa only [controlQuad, add_assoc, add_left_comm, add_comm] using hy
  have heq : y 0 0 + y 1 0 = y 0 1 + y 1 1 := by
    calc
      y 0 0 + y 1 0 =
          (y 0 0 + y 1 0) + ((y 0 1 + y 1 1) + (y 0 1 + y 1 1)) := by
        rw [module_charTwo_add_self, add_zero]
      _ = ((y 0 0 + y 1 0) + (y 0 1 + y 1 1)) + (y 0 1 + y 1 1) := by
        abel
      _ = y 0 1 + y 1 1 := by rw [hsum, zero_add]
  apply hierarchy_branch_of_clifford_pauli_ratio
  · exact branch_actualPaulis_clifford (signedOrderedPauli_actual _ _)
      (signedOrderedPauli_actual _ _)
  · simp only [branchMatrix_conjTranspose, branchMatrix_mul,
      signedOrderedPauli_adjoint, signedOrderedPauli_mul]
    rw [heq]
    exact signedOrderedPauli_same_label_branch _ _ _

theorem twoControlMatrix_signed_affine_dressed_clifford {n : ℕ}
    (s : ZMod 2 → ZMod 2 → ZMod 2) (y : ZMod 2 → ZMod 2 → PauliLabel n)
    (hy : controlQuad y = 0) {C : QuantumMatrix n} (hC : hierarchy n 2 C) :
    hierarchy ((n + 1) + 1) 2
      (twoControlMatrix (fun c b => signedOrderedPauli (s c b) (y c b) * C)) := by
  have hlift : hierarchy ((n + 1) + 1) 2 (twoControlMatrix (fun _ _ => C)) :=
    hierarchy_lift (by omega) (hierarchy_lift (by omega) hC)
  rw [← twoControlMatrix_mul]
  exact hierarchy_clifford_mul_right (by omega) hlift
    (twoControlMatrix_signed_affine_clifford s y hy)

end QuantumProver.ControlledCliffordHierarchy
