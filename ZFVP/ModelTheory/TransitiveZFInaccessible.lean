import ZFVP.ModelTheory.TransitiveZFForcingOrders
import ZFVP.SetTheory.ChoicelessInaccessibleRank

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
namespace TransitiveZF
variable (U : V) [IsTransitive U] [Nonempty (SetDomain U)] [(SetDomain U)↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem cofinalMap_iff (κ X g : SetDomain U) :
    IsCofinalMap κ X g ↔ IsCofinalMap κ.val X.val g.val :=
  bounded_defined_absolute U boundedCofinalMapFormula_bounded
    (fun v ↦ IsCofinalMap (v 0) (v 1) (v 2))
    (fun v ↦ IsCofinalMap (v 0) (v 1) (v 2)) ![κ, X, g]

end TransitiveZF

theorem rank_choicelessInaccessible_iff {ξ : V} [IsOrdinal ξ]
    [Nonempty (SetDomain (hierarchy ξ))] [(SetDomain (hierarchy ξ))↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
    (hs : ∀ β ∈ ξ, succ β ∈ ξ) (κ : SetDomain (hierarchy ξ)) :
    IsChoicelessInaccessible κ ↔ IsChoicelessInaccessible κ.val := by
  let := hierarchy_transitive ξ
  have hh (α : SetDomain (hierarchy ξ)) (hα : IsOrdinal α) :
      (hierarchy α).val = hierarchy α.val := by
    let := (TransitiveZF.ordinal_iff (hierarchy ξ) α).mp hα
    apply TransitiveZF.hierarchy_val (hierarchy ξ) α hα
    exact hierarchy_mono (IsOrdinal.toIsTransitive.transitive _
      (ordinal_mem_hierarchy_iff.mp α.property))
  constructor
  · intro hk
    let := hk.1
    let hk' := (TransitiveZF.ordinal_iff (hierarchy ξ) κ).mp hk.1
    let := hk'
    have hω : (ω : V) ∈ κ.val := by
      have h := hk.2.1
      change (ω : SetDomain (hierarchy ξ)).val ∈ κ.val at h
      simpa only [TransitiveZF.omega_val] using h
    refine ⟨hk', hω, ?_⟩
    intro α hα g hg
    let α' : SetDomain (hierarchy ξ) := ⟨α, (hierarchy_transitive ξ).mem_trans hα κ.property⟩
    have hα' : α' ∈ κ := hα
    let := IsOrdinal.of_mem hα'
    have hH := hh α' inferInstance
    have hHU : hierarchy α ∈ hierarchy ξ := hH ▸ (hierarchy α').property
    have hgU := (hierarchy_transitive ξ).mem_trans hg.1
      (function_mem_hierarchy_limit hs hHU κ.property)
    let g' : SetDomain (hierarchy ξ) := ⟨g, hgU⟩
    apply hk.2.2 α' hα' g'
    apply (TransitiveZF.cofinalMap_iff (hierarchy ξ) κ (hierarchy α') g').mpr
    simpa only [hH] using hg
  · intro hk
    let hki := (TransitiveZF.ordinal_iff (hierarchy ξ) κ).mpr hk.1
    let := hki
    have hω : (ω : SetDomain (hierarchy ξ)) ∈ κ := by
      change (ω : SetDomain (hierarchy ξ)).val ∈ κ.val
      rw [TransitiveZF.omega_val]
      exact hk.2.1
    refine ⟨hki, hω, ?_⟩
    intro α hα g hg
    let := IsOrdinal.of_mem hα
    have hH := hh α inferInstance
    apply hk.2.2 α.val hα g.val
    have hc := (TransitiveZF.cofinalMap_iff (hierarchy ξ) κ (hierarchy α) g).mp hg
    simpa only [hH] using hc

end ZFVP
