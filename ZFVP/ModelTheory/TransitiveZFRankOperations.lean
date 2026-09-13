import ZFVP.ModelTheory.TransitiveZFCardinalSmall
import ZFVP.SetTheory.OrdinalLeftOne
import ZFVP.SetTheory.BoundedFunctionDomain

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
namespace TransitiveZF
variable (U : V) [IsTransitive U] [Nonempty (SetDomain U)] [(SetDomain U)↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem isFunction_iff (p : SetDomain U) : IsFunction p ↔ IsFunction p.val := by
  have he := bounded_defined_absolute U boundedFunctionDomainFormula_bounded
    (fun v ↦ IsFunction (v 0) ∧ domain (v 0) = v 1)
    (fun v ↦ IsFunction (v 0) ∧ domain (v 0) = v 1) ![p, domain p]
  simpa [domain_val U] using he

theorem ordinalLeftOne_val (η : SetDomain U) (hη : IsOrdinal η) :
    (ordinalAdd (1 : SetDomain U) η).val = ordinalAdd (1 : V) η.val := by
  let := hη
  let := (ordinal_iff U η).mp hη
  by_cases hn : η ∈ (ω : SetDomain U)
  · rw [ordinalAdd_one_left_natural hn, succ_val U,
      ordinalAdd_one_left_natural ((natural_iff U η).mp hn)]
  · rw [ordinalAdd_one_left_infinite hn,
      ordinalAdd_one_left_infinite (fun h ↦ hn ((natural_iff U η).mpr h))]

end TransitiveZF

theorem rank_hierarchy_val {ξ : V} [IsOrdinal ξ]
    [Nonempty (SetDomain (hierarchy ξ))] [(SetDomain (hierarchy ξ))↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
    (α : SetDomain (hierarchy ξ)) (hα : IsOrdinal α) :
    (hierarchy α).val = hierarchy α.val := by
  let := hierarchy_transitive ξ
  let := (TransitiveZF.ordinal_iff (hierarchy ξ) α).mp hα
  apply TransitiveZF.hierarchy_val (hierarchy ξ) α hα
  exact hierarchy_mono (IsOrdinal.toIsTransitive.transitive _ (ordinal_mem_hierarchy_iff.mp α.property))

end ZFVP
