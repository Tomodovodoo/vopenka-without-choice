import ZFVP.SetTheory.OrdinalDependentChoice

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem ordinal_choice_for_definable_family {γ : V} [IsOrdinal γ]
    (hDC : InternalDependentChoiceAt γ) (F : V → V) (hF : ℒₛₑₜ-function₁ F)
    (hn : ∀ i ∈ γ, IsNonempty (F i)) :
    ∃ g, IsFunction g ∧ domain g = γ ∧ ∀ i ∈ γ, g ‘ i ∈ F i := by
  rcases eq_empty_or_isNonempty γ with hzero | hγ
  · subst γ
    exact ⟨∅, inferInstance, by simp, by simp⟩
  let A := ⋃ˢ repl F hF γ
  have hinto (i : V) (hi : i ∈ γ) : F i ⊆ A := fun x hx ↦
    mem_sUnion_iff.mpr ⟨F i, (repl_spec hF).mpr ⟨i, hi, rfl⟩, hx⟩
  have hA : IsNonempty A := by
    obtain ⟨i, hi⟩ := hγ
    obtain ⟨x, hx⟩ := hn i hi
    exact ⟨x, hinto i hi x hx⟩
  let R : V := {z ∈ shorterSequences γ A ×ˢ A ; kpair.π₂ z ∈ F (domain (kpair.π₁ z))}
  have hR (s x : V) : ⟨s, x⟩ₖ ∈ R ↔ s ∈ shorterSequences γ A ∧ x ∈ A ∧ x ∈ F (domain s) := by
    simp only [R, mem_sep_iff, kpair_mem_iff, kpair.π₁_kpair, kpair.π₂_kpair]
    tauto
  have hserial : ∀ s ∈ shorterSequences γ A, ∃ x ∈ A, ⟨s, x⟩ₖ ∈ R := by
    intro s hs
    have hd := ((mem_shorterSequences_domain _ _ _).mp hs).1
    obtain ⟨x, hx⟩ := hn (domain s) hd
    have hxA := hinto (domain s) hd x hx
    exact ⟨x, hxA, (hR s x).mpr ⟨hs, hxA, hx⟩⟩
  obtain ⟨g, hg, hstep⟩ := hDC A R hA hserial
  refine ⟨g, IsFunction.of_mem hg, domain_eq_of_mem_function hg, ?_⟩
  intro i hi
  have hh := ((hR _ _).mp (hstep i hi)).2.2
  rwa [domain_eq_of_mem_function
    (function_restrict_mem hg (IsOrdinal.toIsTransitive.transitive _ hi))] at hh

end ZFVP
