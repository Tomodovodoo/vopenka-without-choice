import ZFVP.ModelTheory.FiniteRankLift
import ZFVP.ModelTheory.ForcingModelGraph
import ZFVP.ModelTheory.ForcingRetractionModel

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace FiniteRankLiftData

variable {A B : ForcingContext V} {δ ε e π : V} (L : FiniteRankLiftData A B δ ε e)
  (hπ : IsForcingRetraction A.P A.R B.P B.R π)
  (hG : ∀ p, p ∈ A.G ↔ p ∈ B.G ∧ p ∈ A.P)

noncomputable def nameDomain (_L : FiniteRankLiftData A B δ ε e) : V :=
  {τ ∈ hierarchy δ ; IsForcingName A.P τ}

theorem nameDomain_name {τ : V} (hτ : τ ∈ L.nameDomain) : IsForcingName A.P τ :=
  (mem_sep_iff.mp hτ).2

theorem nameDomain_rank {τ : V} (hτ : τ ∈ L.nameDomain) : τ ∈ hierarchy δ :=
  (mem_sep_iff.mp hτ).1

include hπ

theorem graphName_isName : IsForcingName B.P (nameMapGraph B.one L.nameDomain e) :=
  nameMapGraph_isName B.top.1 (fun _ hτ ↦ (L.nameDomain_name hτ).mono hπ.inclusion)
    (fun _ hτ ↦ L.image_name (L.nameDomain_rank hτ) (L.nameDomain_name hτ))

noncomputable def graph : B.Model := B.mapGraph L.nameDomain e (L.graphName_isName hπ)

include hG in
theorem graph_isFunction : IsFunction (L.graph hπ) := by
  apply B.mapGraph_isFunction L.nameDomain e (L.graphName_isName hπ)
    (fun _ hτ ↦ (L.nameDomain_name hτ).mono hπ.inclusion)
    (fun _ hτ ↦ L.image_name (L.nameDomain_rank hτ) (L.nameDomain_name hτ))
  intro σ hσ τ hτ heq
  let σA : ForcingName A.P := ⟨σ, L.nameDomain_name hσ⟩
  let τA : ForcingName A.P := ⟨τ, L.nameDomain_name hτ⟩
  have hsmall : A.ofName σA = A.ofName τA :=
    ForcingContext.retractionInclusion_injective A B hπ hG heq
  exact (L.image_eq_iff σA τA (L.nameDomain_rank hσ) (L.nameDomain_rank hτ)).mpr hsmall

theorem graph_domain (x : B.Model) : x ∈ domain (L.graph hπ) ↔
    ∃ τ : ForcingName A.P, τ.val ∈ hierarchy δ ∧ x = B.ofName ⟨τ.val, τ.property.mono hπ.inclusion⟩ := by
  rw [graph, B.mem_domain_mapGraph_iff L.nameDomain e (L.graphName_isName hπ)
    (fun _ hτ ↦ (L.nameDomain_name hτ).mono hπ.inclusion)
    (fun _ hτ ↦ L.image_name (L.nameDomain_rank hτ) (L.nameDomain_name hτ))]
  constructor
  · rintro ⟨τ, hτ, he⟩
    exact ⟨⟨τ, L.nameDomain_name hτ⟩, L.nameDomain_rank hτ, he⟩
  · rintro ⟨τ, hτ, he⟩
    exact ⟨τ.val, mem_sep_iff.mpr ⟨hτ, τ.property⟩, he⟩

include hG in
theorem graph_value (τ : ForcingName A.P) (hτ : τ.val ∈ hierarchy δ) :
    (L.graph hπ) ‘ (B.ofName ⟨τ.val, τ.property.mono hπ.inclusion⟩) =
      B.ofName (L.imageName τ hτ) := by
  let : IsFunction (B.mapGraph L.nameDomain e (L.graphName_isName hπ)) := L.graph_isFunction hπ hG
  exact B.mapGraph_value L.nameDomain e (L.graphName_isName hπ)
    (fun _ hσ ↦ (L.nameDomain_name hσ).mono hπ.inclusion)
    (fun _ hσ ↦ L.image_name (L.nameDomain_rank hσ) (L.nameDomain_name hσ))
    (mem_sep_iff.mpr ⟨hτ, τ.property⟩)

theorem graph_domain_transitive : IsTransitive (domain (L.graph hπ)) := by
  let := L.source_inaccessible.1
  let := hierarchy_transitive δ
  constructor
  intro x hx y hy
  obtain ⟨τ, hτ, rfl⟩ := (L.graph_domain hπ x).mp hx
  obtain ⟨ν, p, _, hp, he⟩ := (B.mem_ofName_iff _ y).mp hy
  have hν : ν.val ∈ hierarchy δ :=
    (kpair_components_mem_transitive ((hierarchy_transitive δ).mem_trans hp hτ)).1
  exact (L.graph_domain hπ y).mpr ⟨⟨ν.val, forcingName_subname τ.property hp⟩, hν, he⟩

end FiniteRankLiftData
end ZFVP

