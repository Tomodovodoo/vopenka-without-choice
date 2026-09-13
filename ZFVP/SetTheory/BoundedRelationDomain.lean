import ZFVP.SetTheory.BoundedCodingPrimitives

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def boundedRelationDomainFormula : SetTheorySemisentence 2 :=
  “D f. (∀ x ∈ D, ∃ p ∈ f, ∃ d ∈ p, ∃ y ∈ d, !boundedKpairFormula p x y) ∧
    ∀ p ∈ f, ∀ d ∈ p, ∀ x ∈ d, ∀ e ∈ p, ∀ y ∈ e, !boundedKpairFormula p x y → x ∈ D”

theorem boundedRelationDomainFormula_bounded : IsBoundedSetFormula boundedRelationDomainFormula :=
  .and (.all (.bvar 0) (.exs (.bvar 2) (.exs (.bvar 0) (.exs (.bvar 0)
    (boundedKpairFormula_bounded.subst _)))))
    (.all (.bvar 1) (.all (.bvar 0) (.all (.bvar 0) (.all (.bvar 2) (.all (.bvar 0)
      (.or (boundedKpairFormula_bounded.subst _).neg (.rel _ _)))))))

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance boundedRelationDomainFormula_defined : ℒₛₑₜ-function₁[V] domain via boundedRelationDomainFormula :=
  ⟨fun v ↦ by
    change boundedRelationDomainFormula.Evalb v ↔ v 0 = domain (v 1)
    simp [boundedRelationDomainFormula]
    constructor
    · rintro ⟨hf, hb⟩
      apply mem_ext
      intro x
      constructor
      · intro hx
        obtain ⟨d, y, hp, _, _⟩ := hf x hx
        exact mem_domain_iff.mpr ⟨y, hp⟩
      · intro hx
        obtain ⟨y, hp⟩ := mem_domain_iff.mp hx
        exact hb ⟨x, y⟩ₖ hp (doubleton x y) (by simp [kpair, pair_eq_doubleton])
          x (by simp) (doubleton x y) (by simp [kpair, pair_eq_doubleton]) y (by simp) rfl
    · intro h
      rw [h]
      constructor
      · intro x hx
        obtain ⟨y, hp⟩ := mem_domain_iff.mp hx
        exact ⟨doubleton x y, y, hp, by simp [kpair, pair_eq_doubleton], by simp⟩
      · intro p hp d _ x _ e _ y _ hxy
        exact mem_domain_iff.mpr ⟨y, hxy ▸ hp⟩⟩

end ZFVP
