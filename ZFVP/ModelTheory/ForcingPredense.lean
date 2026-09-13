import ZFVP.ModelTheory.ForcingGeneric

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem externalForcingGeneric_meets_predense {P R D : V} {G : Set V}
    (hG : IsExternalForcingGeneric P R G) (hD : D ⊆ P)
    (hd : ∀ p ∈ P, ∃ q ∈ D, ForcingCompatible P R p q) :
    ∃ q ∈ G, q ∈ D := by
  let E := {r ∈ P ; ∃ q ∈ D, ⟨r, q⟩ₖ ∈ R}
  have hE : ForcingDense P R E := by
    refine ⟨fun r hr ↦ (mem_sep_iff.mp hr).1, ?_⟩
    intro p hp
    obtain ⟨q, hq, r, hr, hrp, hrq⟩ := hd p hp
    exact ⟨r, mem_sep_iff.mpr ⟨hr, q, hq, hrq⟩, hrp⟩
  obtain ⟨r, hrG, hrE⟩ := hG.2 E hE
  obtain ⟨_, q, hq, hrq⟩ := mem_sep_iff.mp hrE
  exact ⟨q, hG.1.2.2.1 r hrG q (hD q hq) hrq, hq⟩

end ZFVP
