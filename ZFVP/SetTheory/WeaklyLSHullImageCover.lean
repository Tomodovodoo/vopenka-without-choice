import ZFVP.SetTheory.WeaklyLSHullFamily

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- A surjective image of a lower rank is contained in a member of the small
hull family, provided that image lies in the target rank. -/
theorem IsWeaklyLSCardinal.hullFamily_cover_surjection {κ α x δ A e : V}
    (hκ : IsWeaklyLSCardinal κ) [IsOrdinal α] (hκα : κ ⊆ α)
    (hx : x ∈ hierarchy α) (hδ : δ ∈ κ)
    (he : e ∈ A ^ hierarchy δ) (hre : range e = A) (hA : A ⊆ hierarchy α) :
    ∃ Z ∈ weaklyLSHullFamily κ α x, A ⊆ Z := by
  have : IsFunction e := IsFunction.of_mem he
  have hd : domain e ⊆ hierarchy δ := by rw [domain_eq_of_mem_function he]
  have hr : range e ⊆ hierarchy α := hre.symm ▸ hA
  obtain ⟨Z, hZ, hxZ, hs, hcover, _⟩ := hκ.hull_for_two_images hδ hκα hx hd hd hr hr
  exact ⟨Z, (mem_weaklyLSHullFamily _ _ _ _).mpr ⟨hZ, hxZ, hs⟩, hre ▸ hcover⟩

end ZFVP
