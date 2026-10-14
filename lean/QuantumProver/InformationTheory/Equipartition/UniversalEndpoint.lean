import QuantumProver.InformationTheory.Equipartition.EndpointAssembly

namespace QuantumProver.Equipartition

theorem universal_logarithmic_endpoint : FiniteModel.UniversalLogarithmicEndpoint := by
  intro d F hF
  exact ⟨FiniteModel.physical_actual_full_rate hF,
    FiniteModel.EndpointAssembly.physical_universal_logarithmic_equipartition hF⟩

end QuantumProver.Equipartition
