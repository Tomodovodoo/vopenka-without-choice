import ZFVP.ModelTheory.CollapseModel
import ZFVP.SetTheory.CountableSets
import ZFVP.SetTheory.WellOrderableSerialHull

/-! Countability and the serial-path step in Usuba, Proposition 3.6.
The surjection onto the interpreted hull is an explicit premise here.
Neither its existence nor the singular-LS hull theorem is asserted. -/

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace CollapseModel
variable {D : V} {G : Set V}
  (hG : IsExternalForcingGeneric (collapseConditions D) (collapseOrder D) G)

theorem check_internallyCountable (hD : IsNonempty D) :
    IsInternallyCountable ((collapseContext D G hG).check D) :=
  internallyCountable_of_surjection internallyCountable_omega
    (genericFunction_mem_function hG hD) (genericFunction_range hG hD)

theorem internallyCountable_of_checked_surjection (hD : IsNonempty D)
    {H e : (collapseContext D G hG).Model}
    (he : e ∈ H ^ (collapseContext D G hG).check D) (hr : range e = H) :
    IsInternallyCountable H :=
  internallyCountable_of_surjection (check_internallyCountable hG hD) he hr

/-- The interpreted hull may contain elements outside the relation's domain.
Its intersection with the domain is countable and supplies the required path. -/
theorem serialPath_of_hull_surjection (hD : IsNonempty D)
    {A R H e : (collapseContext D G hG).Model}
    (he : e ∈ H ^ (collapseContext D G hG).check D) (hr : range e = H)
    (hne : IsNonempty (A ∩ H))
    (hserial : ∀ x ∈ A ∩ H, ∃ y ∈ A ∩ H, ⟨x, y⟩ₖ ∈ R) :
    ∃ f ∈ A ^ (ω : (collapseContext D G hG).Model),
      ∀ n ∈ (ω : (collapseContext D G hG).Model), ⟨f ‘ n, f ‘ (succ n)⟩ₖ ∈ R := by
  have hcount := internallyCountable_of_checked_surjection hG hD he hr
  have hsub : A ∩ H ⊆ H := fun x hx ↦ (mem_inter_iff.mp hx).2
  exact dependentChoice_of_wellOrderable_serial_subset
    (fun x hx ↦ (mem_inter_iff.mp hx).1)
    (internallyCountable_subset hcount hsub).wellOrderable hne hserial

end CollapseModel
end ZFVP
