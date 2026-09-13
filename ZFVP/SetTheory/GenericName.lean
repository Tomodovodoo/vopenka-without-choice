import ZFVP.SetTheory.NameValue

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def genericName (P one : V) : V :=
  repl (fun p ↦ (⟨checkName one p, p⟩ₖ : V)) (by definability) P

theorem mem_genericName_iff (P one z : V) :
    z ∈ genericName P one ↔ ∃ p ∈ P, z = ⟨checkName one p, p⟩ₖ := by
  simp only [genericName, repl_spec]

instance genericName_definable : ℒₛₑₜ-function₂[V] genericName := by
  have h : ℒₛₑₜ-relation₃ (fun C P one : V ↦
      ∀ z, z ∈ C ↔ ∃ p ∈ P, z = ⟨checkName one p, p⟩ₖ) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = genericName (v 1) (v 2) ↔ _
  rw [mem_ext_iff]
  simp only [mem_genericName_iff]

theorem genericName_isName {P one : V} (hone : one ∈ P) : IsForcingName P (genericName P one) := by
  apply (forcingName_iff _ _).mpr
  intro z hz
  obtain ⟨p, hp, rfl⟩ := (mem_genericName_iff _ _ _).mp hz
  exact ⟨checkName one p, p, hp, rfl, checkName_isName hone p⟩

theorem nameValue_genericName {P one G : V} (hone : one ∈ G) (hGP : G ⊆ P) :
    nameValue G (genericName P one) = G := by
  apply SetTheory.mem_ext_iff.mpr
  intro z
  rw [mem_nameValue_iff]
  constructor
  · rintro ⟨σ, p, hp, hσp, he⟩
    obtain ⟨q, _, hpair⟩ := (mem_genericName_iff _ _ _).mp hσp
    obtain ⟨rfl, rfl⟩ := kpair_iff.mp hpair
    rw [nameValue_checkName hone] at he
    exact he ▸ hp
  · intro hz
    exact ⟨checkName one z, z, hz,
      (mem_genericName_iff _ _ _).mpr ⟨z, hGP z hz, rfl⟩, (nameValue_checkName hone z).symm⟩

end ZFVP
