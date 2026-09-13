import ZFVP.SetTheory.BoundedCodingPrimitives

/-! The identity graph has a bounded relational definition. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def boundedIdentityFormula : SetTheorySemisentence 2 :=
  “s Q. (∀ p ∈ s, ∃ x ∈ Q, !boundedKpairFormula p x x) ∧
    ∀ x ∈ Q, !boundedPairMemberFormula s x x”

theorem boundedIdentityFormula_bounded : IsBoundedSetFormula boundedIdentityFormula :=
  .and (.all (.bvar 0) (.exs (.bvar 2) (boundedKpairFormula_bounded.subst _)))
    (.all (.bvar 1) (boundedPairMemberFormula_bounded.subst _))

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance boundedIdentityFormula_defined : ℒₛₑₜ-function₁[V] identity via boundedIdentityFormula :=
  ⟨fun v ↦ by
    change boundedIdentityFormula.Evalb v ↔ v 0 = identity (v 1)
    simp [boundedIdentityFormula]
    constructor
    · rintro ⟨hsub, hfull⟩
      apply mem_ext
      intro p
      rw [mem_identity_iff]
      exact ⟨hsub p, fun ⟨x, hx, he⟩ ↦ he ▸ hfull x hx⟩
    · intro he
      rw [he]
      exact ⟨fun _ ↦ mem_identity_iff.mp, fun x hx ↦ by simp [hx]⟩⟩

end ZFVP
