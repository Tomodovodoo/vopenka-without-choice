import ZFVP.ModelTheory.ClassForcingBoundedQuotientClosure

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
namespace ForcingContext

theorem quotientFamilyValue_definable (A : ForcingContext V) (C L : V) :
    ℒₛₑₜ-function₁ (fun β : A.Model ↦
      {c ∈ (A.check C) ‘ β ; ((A.check L) ‘ β) ‘ c ∈ A.genericSet}) := by
  have h : ℒₛₑₜ-relation (fun b β : A.Model ↦ ∀ c,
    c ∈ b ↔ c ∈ (A.check C) ‘ β ∧ ((A.check L) ‘ β) ‘ c ∈ A.genericSet) := by
    definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = {c ∈ (A.check C) ‘ (v 1) ; ((A.check L) ‘ (v 1)) ‘ c ∈ A.genericSet} ↔ _
  rw [mem_ext_iff]
  simp only [mem_sep_iff]

/-- A family of quotients constructed from checked ground tables. Its
definition never applies a ground class predicate to extension elements. -/
noncomputable def quotientFamily (A : ForcingContext V) (α C L : V) : A.Model :=
  definableGraph (A.check α)
    (fun β ↦ {c ∈ (A.check C) ‘ β ; ((A.check L) ‘ β) ‘ c ∈ A.genericSet})
    (A.quotientFamilyValue_definable C L)

theorem quotientFamily_value (A : ForcingContext V) {α C L β : V}
    (hC : IsFunction C) (hL : IsFunction L)
    (hCdom : domain C = α) (hLdom : domain L = α) (hβ : β ∈ α) :
    (A.quotientFamily α C L) ‘ (A.check β) =
      A.projectionQuotient (C ‘ β) (L ‘ β) := by
  let := hC
  let := hL
  rw [quotientFamily, value_definableGraph _ _ _ ((A.check_mem_iff β α).mpr hβ)]
  simp only [A.check_value (hCdom.symm ▸ hβ), A.check_value (hLdom.symm ▸ hβ)]
  rfl

end ForcingContext
namespace DefinableForcingTower
variable (T : DefinableForcingTower V)

instance boundedProjection_definable : ℒₛₑₜ-function₂ T.boundedProjection := by
  have h : ℒₛₑₜ-relation₃ (fun L i j : V ↦ ∀ z, z ∈ L ↔
    ∃ c ∈ T.boundedConditions j, z = ⟨c, T.projectCondition i c⟩ₖ) := by
    definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = T.boundedProjection (v 1) (v 2) ↔ _
  rw [mem_ext_iff]
  simp only [boundedProjection, mem_definableGraph_iff]

noncomputable def quotientStageFamily (A : ForcingContext V)
    (F : V → V) (hF : ℒₛₑₜ-function₁ F) (i α : V) : A.Model :=
  A.quotientFamily α
    (definableGraph α (fun β ↦ T.boundedConditions (F β)) (by definability))
    (definableGraph α (fun β ↦ T.boundedProjection i (F β)) (by definability))

theorem quotientStageFamily_value (A : ForcingContext V)
    (F : V → V) (hF : ℒₛₑₜ-function₁ F) (i α : V) {β : V} (hβ : β ∈ α) :
    (T.quotientStageFamily A F hF i α) ‘ (A.check β) = T.boundedQuotient A i (F β) := by
  rw [quotientStageFamily, A.quotientFamily_value (by infer_instance) (by infer_instance)
    (domain_definableGraph _ _ _) (domain_definableGraph _ _ _) hβ]
  rw [value_definableGraph _ _ _ hβ, value_definableGraph _ _ _ hβ]
  rfl

end DefinableForcingTower
end ZFVP
