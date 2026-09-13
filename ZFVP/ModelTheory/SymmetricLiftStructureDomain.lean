import ZFVP.ModelTheory.SymmetricLiftOrdinary
import ZFVP.ModelTheory.StructureCode

/-! Every coded structure represented in the lift domain has an internal domain restriction. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace SymmetricLiftData

variable {S : SymmetricContext V} {U W f : V}
variable [IsTransitive U] [IsTransitive W]
variable [Nonempty (SetDomain U)] [Nonempty (SetDomain W)]
variable [(SetDomain U)↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [(SetDomain W)↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable (L : SymmetricLiftData S U W f)

instance graph_domain_transitive : IsTransitive (domain L.graph) := by
  constructor
  intro x hx y hy
  obtain ⟨σ, hσ, rfl⟩ := (L.graph_domain x).mp hx
  obtain ⟨τ, p, _, hp, rfl⟩ := (S.mem_ofName_iff σ y).mp hy
  have hpairU := (inferInstance : IsTransitive U).mem_trans hp hσ
  exact (L.graph_domain _).mpr ⟨τ, (kpair_components_mem_transitive hpairU).1, rfl⟩

theorem structureDomain_subset_graph_domain {language M : S.Model}
    (hM : IsStructureCode language M) (hm : M ∈ domain L.graph) :
    structureDomain M ⊆ domain L.graph := by
  have he : structureCode (structureDomain M) (structureFunctions M) (structureRelations M) ∈ domain L.graph :=
    hM.2.1 ▸ hm
  have hD := (kpair_components_mem_transitive he).1
  exact fun x hx ↦ L.graph_domain_transitive.mem_trans hx hD

theorem exists_structure_restriction {language M : S.Model}
    (hM : IsStructureCode language M) (hm : M ∈ domain L.graph) :
    ∃ e : S.Model, IsFunction e ∧ domain e = structureDomain M ∧
      ∀ x ∈ structureDomain M, ∀ y : L.sourceContext.Model, L.sourceInclusion y = S.toOrdinary x →
        S.toOrdinary (e ‘ x) = L.targetInclusion (L.ordinaryLift y) := by
  apply L.exists_internal_restriction (structureDomain M)
  intro x hx
  exact (L.graph_domain x).mp (L.structureDomain_subset_graph_domain hM hm x hx)

end SymmetricLiftData
end ZFVP
