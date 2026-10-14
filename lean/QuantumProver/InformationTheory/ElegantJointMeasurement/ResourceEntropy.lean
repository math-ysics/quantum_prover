import Mathlib

namespace QuantumProver.ElegantJointMeasurement.Entropy

open scoped BigOperators

noncomputable def entropyBits {ι : Type*} [Fintype ι] (p : ι → ℝ) : ℝ :=
  (∑ i, Real.negMulLog (p i)) / Real.log 2

noncomputable def binaryEntropyBits (x : ℝ) : ℝ :=
  Real.binEntropy x / Real.log 2

noncomputable def splitWeights {ι : Type*} (x : ℝ) (μ : ι → ℝ) : Option ι → ℝ
  | none => x
  | some i => (1 - x) * μ i

noncomputable def purity {ι : Type*} [Fintype ι] (p : ι → ℝ) : ℝ := ∑ i, (p i) ^ 2

end QuantumProver.ElegantJointMeasurement.Entropy
