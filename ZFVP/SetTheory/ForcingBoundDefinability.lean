import ZFVP.SetTheory.ForcingBoundSectionCompatibility

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

private def boundLaw (P R π i I θ B : V) : Prop :=
  (∀ j ∈ θ, i ⊆ j → ∀ f, IsForcingDirectedFamily (P ‘ j) (R ‘ j) I f →
    ∀ p ∈ P ‘ i, (∀ a ∈ I, ⟨p, (π ‘ ⟨i, j⟩ₖ) ‘ (f ‘ a)⟩ₖ ∈ R ‘ i) →
      (B ‘ j) ‘ ⟨f, p⟩ₖ ∈ P ‘ j ∧
      (∀ a ∈ I, ⟨(B ‘ j) ‘ ⟨f, p⟩ₖ, f ‘ a⟩ₖ ∈ R ‘ j) ∧
      (π ‘ ⟨i, j⟩ₖ) ‘ ((B ‘ j) ‘ ⟨f, p⟩ₖ) = p)

private instance boundLaw_definable (P R π i I : V) : ℒₛₑₜ-relation[V] (boundLaw P R π i I) := by
  unfold boundLaw
  definability

private def boundCommuteLaw (P R π i I θ B : V) : Prop :=
  (∀ j ∈ θ, ∀ k ∈ θ, i ⊆ j → j ⊆ k →
    ∀ f, IsForcingDirectedFamily (P ‘ k) (R ‘ k) I f → ∀ p ∈ P ‘ i,
    (∀ a ∈ I, ⟨p, (π ‘ ⟨i, k⟩ₖ) ‘ (f ‘ a)⟩ₖ ∈ R ‘ i) →
      (π ‘ ⟨j, k⟩ₖ) ‘ ((B ‘ k) ‘ ⟨f, p⟩ₖ) =
        (B ‘ j) ‘ ⟨compose f (π ‘ ⟨j, k⟩ₖ), p⟩ₖ)

private instance boundCommuteLaw_definable (P R π i I : V) : ℒₛₑₜ-relation[V] (boundCommuteLaw P R π i I) := by
  unfold boundCommuteLaw
  definability

private def boundSectionLaw (P R π E i I θ B : V) : Prop :=
  (∀ j ∈ θ, ∀ k ∈ θ, i ⊆ j → j ⊆ k →
    ∀ f, IsForcingDirectedFamily (P ‘ j) (R ‘ j) I f → ∀ p ∈ P ‘ i,
    (∀ a ∈ I, ⟨p, (π ‘ ⟨i, j⟩ₖ) ‘ (f ‘ a)⟩ₖ ∈ R ‘ i) →
      (B ‘ k) ‘ ⟨compose f (E ‘ ⟨j, k⟩ₖ), p⟩ₖ = (E ‘ ⟨j, k⟩ₖ) ‘ ((B ‘ j) ‘ ⟨f, p⟩ₖ))

private instance boundSectionLaw_definable (P R π E i I : V) : ℒₛₑₜ-relation[V] (boundSectionLaw P R π E i I) := by
  unfold boundSectionLaw
  definability

instance coherentForcingBound_definable (P R π i I : V) :
    ℒₛₑₜ-relation[V] (fun θ B ↦ IsCoherentForcingBound θ P R π B i I) := by
  have hd : ℒₛₑₜ-relation[V] (fun θ B ↦ boundLaw P R π i I θ B ∧ boundCommuteLaw P R π i I θ B) := by definability
  apply Language.Definable.of_iff hd
  intro v
  exact ⟨fun h ↦ ⟨h.bound, h.commute⟩, fun h ↦ ⟨h.1, h.2⟩⟩

instance sectionCompatibleForcingBound_definable (P R π E i I : V) :
    ℒₛₑₜ-relation[V] (fun θ B ↦ IsSectionCompatibleForcingBound θ P R π E B i I) := by
  apply Language.Definable.of_iff (boundSectionLaw_definable P R π E i I)
  intro v
  exact ⟨fun h ↦ h.compatible, fun h ↦ ⟨h⟩⟩

end ZFVP
