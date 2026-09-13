import ZFVP.SetTheory.ForcingNames
import ZFVP.SetTheory.ForcingOrder

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def forcingUnionName (P R τ : V) : V :=
  {z ∈ nameClosure τ ×ˢ P ; ∃ σ s t, ⟨σ, s⟩ₖ ∈ τ ∧
    ⟨kpair.π₁ z, t⟩ₖ ∈ σ ∧ ⟨kpair.π₂ z, s⟩ₖ ∈ R ∧ ⟨kpair.π₂ z, t⟩ₖ ∈ R}

theorem mem_forcingUnionName_iff (P R τ ν q : V) :
    ⟨ν, q⟩ₖ ∈ forcingUnionName P R τ ↔ q ∈ P ∧
      ∃ σ s t, ⟨σ, s⟩ₖ ∈ τ ∧ ⟨ν, t⟩ₖ ∈ σ ∧ ⟨q, s⟩ₖ ∈ R ∧ ⟨q, t⟩ₖ ∈ R := by
  simp only [forcingUnionName, mem_sep_iff, kpair_mem_iff, kpair.π₁_kpair, kpair.π₂_kpair]
  constructor
  · rintro ⟨⟨_, hq⟩, h⟩
    exact ⟨hq, h⟩
  · rintro ⟨hq, σ, s, t, hσ, hν, hqs, hqt⟩
    exact ⟨⟨nameClosure_mem_mono (subname_mem_nameClosure hσ) _
      (subname_mem_nameClosure hν), hq⟩, σ, s, t, hσ, hν, hqs, hqt⟩

theorem forcingUnionName_isName {P R τ : V} (hτ : IsForcingName P τ) :
    IsForcingName P (forcingUnionName P R τ) := by
  apply (forcingName_iff _ _).mpr
  intro z hz
  obtain ⟨hzB, _⟩ := mem_sep_iff.mp hz
  obtain ⟨ν, _, q, hq, rfl⟩ := mem_prod_iff.mp hzB
  obtain ⟨_, σ, s, t, hσ, hν, _, _⟩ := (mem_forcingUnionName_iff _ _ _ _ _).mp hz
  exact ⟨ν, q, hq, rfl, forcingName_subname (forcingName_subname hτ hσ) hν⟩

end ZFVP
