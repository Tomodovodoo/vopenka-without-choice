import ZFVP.ModelTheory.InternalGenericTruth
import ZFVP.Syntax.EndExtensionBoundedCodes

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
namespace ForcingContext

theorem evaluationRange_transitive (A : ForcingContext V) (D : V)
    (hD : ∀ τ ∈ D, IsForcingName A.P τ)
    (hc : ∀ τ ∈ D, ∀ u p, ⟨u, p⟩ₖ ∈ τ → u ∈ D) :
    IsTransitive (range (A.evaluationGraph D hD)) := by
  constructor
  intro x hx y hy
  obtain ⟨τ, hτ, rfl⟩ := (A.mem_range_evaluationGraph_iff D hD x).mp hx
  obtain ⟨ν, p, _, hp, rfl⟩ := (A.mem_ofName_iff _ y).mp hy
  exact (A.mem_range_evaluationGraph_iff D hD _).mpr ⟨ν.val, hc τ hτ ν.val p hp, rfl⟩

theorem evaluationRange_nonempty (A : ForcingContext V) (D : V)
    (hD : ∀ τ ∈ D, IsForcingName A.P τ) (hne : IsNonempty D) :
    IsNonempty (range (A.evaluationGraph D hD)) := by
  obtain ⟨τ, hτ⟩ := hne.nonempty
  exact ⟨_, (A.mem_range_evaluationGraph_iff D hD _).mpr ⟨τ, hτ, rfl⟩⟩

theorem bounded_internalGenericTruth (A : ForcingContext V) (D : V)
    (hD : ∀ τ ∈ D, IsForcingName A.P τ) (hne : IsNonempty D)
    (hc : ∀ τ ∈ D, ∀ u p, ⟨u, p⟩ₖ ∈ τ → u ∈ D)
    {n φ b : V} (hφ : IsBoundedFormulaCode n φ) (hb : b ∈ D ^ n) :
    BoundedTruth (A.check n) (A.check φ) (A.sequenceValue b (A.nameSequence_of_mem_function hD hb)) ↔
      GenericMeets A.G (internalForcingSet A.P A.R D n φ b) := by
  let := A.evaluationRange_transitive D hD hc
  have hφ' : IsBoundedFormulaCode (A.check n) (A.check φ) := (A.checkEmbedding.boundedFormulaCode_iff n φ).mp hφ
  exact (boundedTruth_iff_membershipSatisfies hφ' (A.evaluationRange_nonempty D hD hne)
    (A.sequenceValue_mem_evaluationRange hD hb)).trans
      (A.groundGenericTruth D hD (boundedFormulaFamily_subset _ hφ) b hb)

end ForcingContext
end ZFVP
