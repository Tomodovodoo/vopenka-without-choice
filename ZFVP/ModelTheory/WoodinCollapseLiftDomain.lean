import ZFVP.ModelTheory.WoodinCollapseLift
import ZFVP.ModelTheory.SuccessorRankLiftSequences
import ZFVP.ModelTheory.ForcingChoice
import ZFVP.SetTheory.BoundedGraphDependentChoice

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem SuccessorRankLiftData.graph_boundedElementary {A B : ForcingContext V} {ρ γ e π : V}
    (L : SuccessorRankLiftData A B ρ γ e) (hπ : IsForcingRetraction A.P A.R B.P B.R π)
    (hG : ∀ p, p ∈ A.G ↔ p ∈ B.G ∧ p ∈ A.P) : IsBoundedElementaryGraph (L.graph hπ) :=
  ⟨L.graph_isFunction hπ hG, L.graph_domain_transitive hπ, fun hφ v hv ↦ L.graph_bounded_iff hπ hG hφ v hv⟩

namespace WoodinCollapseModel

variable {κ δ : V} (hκ : IsRegularCardinal κ) [IsOrdinal δ] {G : Set V}
  (hG : IsExternalForcingGeneric (woodinCollapse κ δ) (woodinCollapseOrder κ δ) G)

theorem check_hierarchy_wellOrderable {ρ : V} (hρ : Cn 1 ρ) (hρδ : ρ ∈ δ) :
    IsWellOrderable ((woodinCollapseContext hκ δ G hG).check (hierarchy ρ)) := by
  let := hρ.ordinal
  have hn : ρ ∉ (ω : V) := by
    intro h
    exact mem_irrefl ρ (IsOrdinal.toIsTransitive.mem_trans h hρ.omega_lt)
  have he := ordinalAdd_one_left_infinite hn
  have hsub : hierarchy (ordinalAdd (1 : V) ρ) ⊆ hierarchy δ := by
    rw [he]
    exact hierarchy_mono (IsOrdinal.toIsTransitive.transitive _ hρδ)
  simpa only [he] using check_row_wellOrderable hκ hG hρδ hsub

theorem lowerName_wellOrderable {ρ : V} (hρ : Cn 1 ρ) (hρδ : ρ ∈ δ)
    (τ : ForcingName (woodinCollapse κ δ)) (hτ : τ.val ∈ hierarchy ρ) :
    IsWellOrderable ((woodinCollapseContext hκ δ G hG).ofName τ) := by
  let S := woodinCollapseContext hκ δ G hG
  let := hρ.ordinal
  have hsub : nameClosure τ.val ⊆ hierarchy ρ :=
    nameClosure_minimal (transitive_subnameClosed (hierarchy_transitive ρ)) hτ
  apply S.ofName_wellOrderable_of_closure τ
  exact wellOrderable_of_cardLE (cardLE_of_subset ((S.checkEmbedding.subset_iff _ _).mpr hsub))
    (check_hierarchy_wellOrderable hκ hG hρ hρδ)

theorem liftedDomain_wellOrderable {A : ForcingContext V} {ρ γ e π : V}
    (L : SuccessorRankLiftData A (woodinCollapseContext hκ δ G hG) ρ γ e)
    (hπ : IsForcingRetraction A.P A.R (woodinCollapse κ δ) (woodinCollapseOrder κ δ) π)
    (hρδ : ρ ∈ δ) {X : (woodinCollapseContext hκ δ G hG).Model}
    (hX : X ∈ domain (L.graph hπ)) : IsWellOrderable X := by
  obtain ⟨τ, hτ, rfl⟩ := (L.graph_domain hπ X).mp hX
  exact lowerName_wellOrderable hκ hG L.source_correct hρδ
    ⟨τ.val, τ.property.mono hπ.inclusion⟩ hτ

end WoodinCollapseModel
end ZFVP
