import ZFVP.ModelTheory.SchmerlInternalTaggedTrees
import ZFVP.SetTheory.FunctionUnion
import ZFVP.SetTheory.EndExtensionWellOrdering

/-! Checked names commute with the actual tagged tree construction. -/

set_option autoImplicit false

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
open Schmerl
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace ForcingContext

theorem check_internalTaggedTree (F : ForcingContext V) {J D : V} [IsFunction D]
    (hD : J ⊆ domain D) :
    F.check (internalTaggedTree J D) = internalTaggedTree (F.check J) (F.check D) := by
  ext p
  constructor
  · intro hp
    obtain ⟨q, hq, rfl⟩ := (F.mem_check_iff _ p).mp hp
    obtain ⟨j, hj, x, hx, rfl⟩ := (mem_internalTaggedTree _ _ _).mp hq
    rw [F.check_kpair]
    exact pair_mem_internalTaggedTree.mpr ⟨(F.check_mem_iff _ _).mpr hj, by
      rw [F.check_value (hD j hj)]
      exact (F.check_mem_iff _ _).mpr hx⟩
  · intro hp
    obtain ⟨a, ha, b, hb, rfl⟩ := (mem_internalTaggedTree _ _ _).mp hp
    obtain ⟨j, hj, rfl⟩ := (F.mem_check_iff J a).mp ha
    rw [F.check_value (hD j hj)] at hb
    obtain ⟨x, hx, rfl⟩ := (F.mem_check_iff (D ‘ j) b).mp hb
    rw [← F.check_kpair, F.check_mem_iff]
    exact pair_mem_internalTaggedTree.mpr ⟨hj, hx⟩

theorem check_internalTaggedTreeOrder_iff (F : ForcingContext V) {J D S p q : V}
    [IsFunction D] [IsFunction S] (hD : J ⊆ domain D) (hS : J ⊆ domain S)
    (hp : p ∈ internalTaggedTree J D) (hq : q ∈ internalTaggedTree J D) :
    ⟨F.check p, F.check q⟩ₖ ∈ internalTaggedTreeOrder (F.check J) (F.check D) (F.check S) ↔
      ⟨p, q⟩ₖ ∈ internalTaggedTreeOrder J D S := by
  obtain ⟨j, hj, x, hx, rfl⟩ := (mem_internalTaggedTree _ _ _).mp hp
  obtain ⟨k, hk, y, hy, rfl⟩ := (mem_internalTaggedTree _ _ _).mp hq
  simp only [F.check_kpair, pair_mem_internalTaggedTreeOrder,
    F.check_value (hD j hj), F.check_value (hD k hk), F.check_value (hS j hj),
    F.check_mem_iff, F.check_eq_iff, F.check_relation_iff]

theorem check_internalTaggedTreeOrder (F : ForcingContext V) {J D S : V}
    [IsFunction D] [IsFunction S] (hD : J ⊆ domain D) (hS : J ⊆ domain S) :
    F.check (internalTaggedTreeOrder J D S) = internalTaggedTreeOrder (F.check J) (F.check D) (F.check S) := by
  ext p
  constructor
  · intro hp
    obtain ⟨q, hq, rfl⟩ := (F.mem_check_iff _ p).mp hp
    obtain ⟨x, hx, y, hy, rfl⟩ := mem_prod_iff.mp (internalTaggedTreeOrder_subset _ _ _ q hq)
    rw [F.check_kpair]
    exact (F.check_internalTaggedTreeOrder_iff hD hS hx hy).mpr hq
  · intro hp
    obtain ⟨x, hx, y, hy, rfl⟩ := mem_prod_iff.mp (internalTaggedTreeOrder_subset _ _ _ p hp)
    rw [← F.check_internalTaggedTree hD] at hx hy
    obtain ⟨a, ha, rfl⟩ := (F.mem_check_iff _ x).mp hx
    obtain ⟨b, hb, rfl⟩ := (F.mem_check_iff _ y).mp hy
    rw [← F.check_kpair, F.check_mem_iff]
    exact (F.check_internalTaggedTreeOrder_iff hD hS ha hb).mp hp

theorem check_internalTaggedTreeRank (F : ForcingContext V) {J D S κ r : V}
    [IsFunction D] [IsFunction r] (hD : J ⊆ domain D) (hr : J ⊆ domain r)
    (hT : ∀ j ∈ J, InternalRankedTree (D ‘ j) (S ‘ j) κ (r ‘ j)) :
    F.check (internalTaggedTreeRank J D r) = internalTaggedTreeRank (F.check J) (F.check D) (F.check r) := by
  apply functions_eq_of_domain_values
  · rw [F.check_domain, domain_internalTaggedTreeRank, domain_internalTaggedTreeRank,
      F.check_internalTaggedTree hD]
  · intro p hp
    rw [F.check_domain, domain_internalTaggedTreeRank] at hp
    obtain ⟨q, hq, rfl⟩ := (F.mem_check_iff _ p).mp hp
    obtain ⟨j, hj, x, hx, rfl⟩ := (mem_internalTaggedTree _ _ _).mp hq
    let : IsFunction (r ‘ j) := IsFunction.of_mem (hT j hj).rank_function
    have hj' := (F.check_mem_iff j J).mpr hj
    have hx' : F.check x ∈ (F.check D) ‘ (F.check j) := by
      rw [F.check_value (hD j hj)]
      exact (F.check_mem_iff _ _).mpr hx
    rw [F.check_value (by rw [domain_internalTaggedTreeRank]; exact pair_mem_internalTaggedTree.mpr ⟨hj, hx⟩),
      internalTaggedTreeRank_value hj hx, F.check_kpair, internalTaggedTreeRank_value hj' hx',
      F.check_value (hr j hj), F.check_value ((domain_eq_of_mem_function (hT j hj).rank_function).symm ▸ hx)]

theorem check_taggedSet (F : ForcingContext V) (j B : V) :
    F.check (({j} : V) ×ˢ B) = ({F.check j} : F.Model) ×ˢ F.check B := by
  have he := F.checkEmbedding.map_prod ({j} : V) B
  change F.check (({j} : V) ×ˢ B) = F.check ({j} : V) ×ˢ F.check B at he
  simpa only [F.check_singleton] using he

end ForcingContext
end ZFVP
