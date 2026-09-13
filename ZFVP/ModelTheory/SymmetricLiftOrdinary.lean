import ZFVP.ModelTheory.SymmetricLift
import ZFVP.ModelTheory.ForcingLift
import ZFVP.ModelTheory.ForcingQuotientInclusion

/-! Identify the internal symmetric graph with the ordinary lift on its domain. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace SymmetricLiftData

variable {S : SymmetricContext V} {U W f : V}
variable (L : SymmetricLiftData S U W f)

include L

theorem target_poset_mem : S.P ∈ W := by
  have h := (L.embedding.toFunction ⟨S.P, L.poset_mem⟩).property
  change f ‘ S.P ∈ W at h
  exact L.fix_poset ▸ h

theorem target_relation_mem : S.R ∈ W := by
  have h := (L.embedding.toFunction ⟨S.R, L.relation_mem⟩).property
  change f ‘ S.R ∈ W at h
  exact L.fix_relation ▸ h

variable [IsTransitive U] [IsTransitive W]
variable [Nonempty (SetDomain U)] [Nonempty (SetDomain W)]
variable [(SetDomain U)↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [(SetDomain W)↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def sourceContext : ForcingContext (SetDomain U) :=
  TransitiveZF.externalForcingContext U ⟨S.P, L.poset_mem⟩ ⟨S.R, L.relation_mem⟩
    ⟨S.one, (inferInstance : IsTransitive U).mem_trans S.top.1 L.poset_mem⟩ S.G S.order S.top S.generic

def targetContext : ForcingContext (SetDomain W) :=
  TransitiveZF.externalForcingContext W ⟨S.P, L.target_poset_mem⟩ ⟨S.R, L.target_relation_mem⟩
    ⟨S.one, (inferInstance : IsTransitive W).mem_trans S.top.1 L.target_poset_mem⟩ S.G S.order S.top S.generic

theorem ordinaryLiftData : ForcingContext.LiftData L.sourceContext L.targetContext L.embedding.toElementaryMap := by
  refine ⟨Subtype.ext L.fix_poset, Subtype.ext L.fix_relation, ?_⟩
  intro p hp
  change f ‘ p.val ∈ S.G
  rw [L.fix_conditions p.val (S.generic.1.1 p.val hp)]
  exact hp

noncomputable def ordinaryLift : ElementaryMap L.sourceContext.Model L.targetContext.Model :=
  L.ordinaryLiftData.elementaryLift

noncomputable def sourceInclusion : MembershipEndExtension L.sourceContext.Model S.toForcingContext.Model :=
  TransitiveZF.forcingQuotientEndExtension U ⟨S.P, L.poset_mem⟩ ⟨S.R, L.relation_mem⟩ S.G S.order S.generic

noncomputable def targetInclusion : MembershipEndExtension L.targetContext.Model S.toForcingContext.Model :=
  TransitiveZF.forcingQuotientEndExtension W ⟨S.P, L.target_poset_mem⟩ ⟨S.R, L.target_relation_mem⟩ S.G S.order S.generic

noncomputable def sourceValue (σ : S.Name) (hσ : σ.val ∈ U) : L.sourceContext.Model :=
  L.sourceContext.ofName ⟨⟨σ.val, hσ⟩, (TransitiveZF.forcingName_iff U ⟨S.P, L.poset_mem⟩ ⟨σ.val, hσ⟩).mpr σ.property.1⟩

omit [IsTransitive W] [Nonempty (SetDomain W)] [(SetDomain W)↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
theorem sourceInclusion_sourceValue (σ : S.Name) (hσ : σ.val ∈ U) :
    L.sourceInclusion (L.sourceValue σ hσ) = S.toOrdinary (S.ofName σ) := rfl

theorem ordinaryLift_graph_value (σ : S.Name) (hσ : σ.val ∈ U) :
    L.targetInclusion (L.ordinaryLift (L.sourceValue σ hσ)) = S.toOrdinary (L.graph ‘ (S.ofName σ)) := by
  rw [L.graph_value σ hσ]
  rfl

theorem graph_domain_source (x : S.Model) (hx : x ∈ domain L.graph) :
    ∃ y : L.sourceContext.Model, L.sourceInclusion y = S.toOrdinary x := by
  obtain ⟨σ, hσ, rfl⟩ := (L.graph_domain x).mp hx
  exact ⟨L.sourceValue σ hσ, L.sourceInclusion_sourceValue σ hσ⟩

theorem graph_agrees_ordinaryLift (x : S.Model) (hx : x ∈ domain L.graph)
    (y : L.sourceContext.Model) (hy : L.sourceInclusion y = S.toOrdinary x) :
    S.toOrdinary (L.graph ‘ x) = L.targetInclusion (L.ordinaryLift y) := by
  obtain ⟨σ, hσ, rfl⟩ := (L.graph_domain x).mp hx
  have hey : y = L.sourceValue σ hσ :=
    L.sourceInclusion.injective (hy.trans (L.sourceInclusion_sourceValue σ hσ).symm)
  rw [hey]
  exact (L.ordinaryLift_graph_value σ hσ).symm

theorem exists_internal_restriction (A : S.Model)
    (hA : ∀ x ∈ A, ∃ σ : S.Name, σ.val ∈ U ∧ x = S.ofName σ) :
    ∃ g : S.Model, IsFunction g ∧ domain g = A ∧
      ∀ x ∈ A, ∀ y : L.sourceContext.Model, L.sourceInclusion y = S.toOrdinary x →
        S.toOrdinary (g ‘ x) = L.targetInclusion (L.ordinaryLift y) := by
  have hdom : A ⊆ domain L.graph := fun x hx ↦ (L.graph_domain x).mpr (hA x hx)
  refine ⟨L.graph ↾ A, inferInstance, ?_, ?_⟩
  · apply SetTheory.mem_ext_iff.mpr
    intro x
    rw [domain_restrict_eq, mem_inter_iff]
    exact ⟨And.right, fun hx ↦ ⟨hdom x hx, hx⟩⟩
  · intro x hx y hy
    rw [value_restrict (hdom x hx) hx]
    exact L.graph_agrees_ordinaryLift x (hdom x hx) y hy

end SymmetricLiftData
end ZFVP
