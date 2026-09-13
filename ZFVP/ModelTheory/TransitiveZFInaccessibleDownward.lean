import ZFVP.ModelTheory.TransitiveZFInaccessible

/-! Inaccessibility descends to a transitive ZF model containing the full lower hierarchy. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace TransitiveZF

theorem choicelessInaccessible_downward (M : V) [IsTransitive M]
    [Nonempty (SetDomain M)] [(SetDomain M)↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
    (γ : SetDomain M) (hγ : IsChoicelessInaccessible γ.val)
    (hsub : hierarchy γ.val ⊆ M) : IsChoicelessInaccessible γ := by
  let hγi := (ordinal_iff M γ).mpr hγ.1
  let := hγi
  let := hγ.1
  have hω : (ω : SetDomain M) ∈ γ := by
    change (ω : SetDomain M).val ∈ γ.val
    rw [omega_val]
    exact hγ.2.1
  refine ⟨hγi, hω, ?_⟩
  intro α hα g hg
  let hαi := IsOrdinal.of_mem hα
  let := hαi
  let := (ordinal_iff M α).mp hαi
  have hαγ : α.val ∈ γ.val := hα
  have hH : (hierarchy α).val = hierarchy α.val :=
    hierarchy_val M α hαi (fun x hx ↦ hsub x
      (hierarchy_mono (IsOrdinal.toIsTransitive.transitive _ hαγ) x hx))
  apply hγ.2.2 α.val hα g.val
  have hc := (cofinalMap_iff M γ (hierarchy α) g).mp hg
  simpa only [hH] using hc

end TransitiveZF

end ZFVP
