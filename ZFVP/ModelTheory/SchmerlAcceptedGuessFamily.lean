import ZFVP.ModelTheory.InternalNamedSeparationOmission
import ZFVP.SetTheory.CountableSets

/-! Diamond guesses accepted along an actual coded history form an actual
countable family. The preservation invariant supplies the successor input. -/

set_option autoImplicit false

namespace ZFVP.Schmerl
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def guessedU (A C β : V) : V := (A ‘ β) ∩ structureDomain (C ‘ β)
noncomputable def guessedW (A C β : V) : V := structureDomain (C ‘ β) \ guessedU A C β

instance guessedU_definable : ℒₛₑₜ-function₃[V] guessedU := by unfold guessedU; definability
instance guessedW_definable : ℒₛₑₜ-function₃[V] guessedW := by unfold guessedW; definability

theorem guessedU_subset (A C β : V) : guessedU A C β ⊆ structureDomain (C ‘ β) :=
  fun _ hx ↦ (mem_inter_iff.mp hx).2

theorem guessedW_subset (A C β : V) : guessedW A C β ⊆ structureDomain (C ‘ β) :=
  fun _ hx ↦ (mem_sdiff_iff.mp hx).1

noncomputable def acceptedGuessIndices (θ C A : V) : V :=
  {β ∈ θ ; IsCodedInseparable (C ‘ β) (guessedU A C β) (guessedW A C β)}

theorem mem_acceptedGuessIndices (θ C A β : V) :
    β ∈ acceptedGuessIndices θ C A ↔
      β ∈ θ ∧ IsCodedInseparable (C ‘ β) (guessedU A C β) (guessedW A C β) := mem_sep_iff

instance acceptedGuessIndices_definable : ℒₛₑₜ-function₃[V] acceptedGuessIndices := by
  have hh : ℒₛₑₜ-relation₄[V] (fun I θ C A ↦ ∀ β, β ∈ I ↔
      β ∈ θ ∧ IsCodedInseparable (C ‘ β) (guessedU A C β) (guessedW A C β)) := by definability
  apply Language.Definable.of_iff hh
  intro v
  rw [mem_ext_iff]
  simp only [mem_acceptedGuessIndices]
  rfl

noncomputable def acceptedGuessFamily (θ C A : V) : V :=
  repl (fun β ↦ ⟨guessedU A C β, guessedW A C β⟩ₖ) (by definability)
    (acceptedGuessIndices θ C A)

theorem mem_acceptedGuessFamily (θ C A p : V) :
    p ∈ acceptedGuessFamily θ C A ↔
      ∃ β ∈ θ, IsCodedInseparable (C ‘ β) (guessedU A C β) (guessedW A C β) ∧
        p = ⟨guessedU A C β, guessedW A C β⟩ₖ := by
  simp only [acceptedGuessFamily, repl_spec, mem_acceptedGuessIndices]
  constructor
  · rintro ⟨β, ⟨hβ, hacc⟩, hp⟩
    exact ⟨β, hβ, hacc, hp⟩
  · rintro ⟨β, hβ, hacc, hp⟩
    exact ⟨β, ⟨hβ, hacc⟩, hp⟩

theorem pair_mem_acceptedGuessFamily (θ C A U W : V) :
    ⟨U, W⟩ₖ ∈ acceptedGuessFamily θ C A ↔
      ∃ β ∈ θ, IsCodedInseparable (C ‘ β) (guessedU A C β) (guessedW A C β) ∧
        U = guessedU A C β ∧ W = guessedW A C β := by
  rw [mem_acceptedGuessFamily]
  constructor
  · rintro ⟨β, hβ, hacc, heq⟩
    exact ⟨β, hβ, hacc, kpair_inj heq⟩
  · rintro ⟨β, hβ, hacc, rfl, rfl⟩
    exact ⟨β, hβ, hacc, rfl⟩

instance acceptedGuessFamily_definable : ℒₛₑₜ-function₃[V] acceptedGuessFamily := by
  have hh : ℒₛₑₜ-relation₄[V] (fun F θ C A ↦ ∀ p, p ∈ F ↔
      ∃ β ∈ θ, IsCodedInseparable (C ‘ β) (guessedU A C β) (guessedW A C β) ∧
        p = ⟨guessedU A C β, guessedW A C β⟩ₖ) := by definability
  apply Language.Definable.of_iff hh
  intro v
  rw [mem_ext_iff]
  simp only [mem_acceptedGuessFamily]
  rfl

theorem acceptedGuessFamily_countable {θ C A : V} (hθ : IsInternallyCountable θ) :
    IsInternallyCountable (acceptedGuessFamily θ C A) :=
  internallyCountable_repl _ _ (internallyCountable_subset hθ (fun _ hβ ↦ (mem_sep_iff.mp hβ).1))

theorem acceptedGuessFamily_mono {θ δ C A : V} (hθδ : θ ⊆ δ) :
    acceptedGuessFamily θ C A ⊆ acceptedGuessFamily δ C A := by
  intro p hp
  obtain ⟨β, hβ, hacc, hp⟩ := (mem_acceptedGuessFamily θ C A p).mp hp
  exact (mem_acceptedGuessFamily δ C A p).mpr ⟨β, hθδ β hβ, hacc, hp⟩

def PreservesAcceptedGuesses (θ C A : V) : Prop :=
  ∀ β ∈ θ, ∀ γ ∈ θ, β ⊆ γ →
    IsCodedInseparable (C ‘ β) (guessedU A C β) (guessedW A C β) →
    IsCodedInseparable (C ‘ γ) (guessedU A C β) (guessedW A C β)

instance preservesAcceptedGuesses_definable : ℒₛₑₜ-relation₃[V] PreservesAcceptedGuesses := by
  unfold PreservesAcceptedGuesses
  definability

theorem PreservesAcceptedGuesses.mono {θ δ C A : V}
    (h : PreservesAcceptedGuesses δ C A) (hθδ : θ ⊆ δ) : PreservesAcceptedGuesses θ C A :=
  fun β hβ γ hγ hβγ hacc ↦ h β (hθδ β hβ) γ (hθδ γ hγ) hβγ hacc

theorem PreservesAcceptedGuesses.family_at {θ C A α : V}
    (h : PreservesAcceptedGuesses θ C A) (hα : α ∈ θ)
    (hlast : ∀ β ∈ θ, β ⊆ α) :
    ∀ U W, ⟨U, W⟩ₖ ∈ acceptedGuessFamily θ C A → IsCodedInseparable (C ‘ α) U W := by
  intro U W hp
  obtain ⟨β, hβ, hacc, rfl, rfl⟩ := (pair_mem_acceptedGuessFamily θ C A U W).mp hp
  exact h β hβ α hα (hlast β hβ) hacc

theorem PreservesAcceptedGuesses.family_at_successor {α C A : V} [IsOrdinal α]
    (h : PreservesAcceptedGuesses (succ α) C A) :
    ∀ U W, ⟨U, W⟩ₖ ∈ acceptedGuessFamily (succ α) C A → IsCodedInseparable (C ‘ α) U W := by
  apply h.family_at (mem_succ_iff.mpr (Or.inl rfl))
  intro β hβ
  rcases mem_succ_iff.mp hβ with rfl | hβ
  · exact subset_refl _
  · exact IsTransitive.transitive β hβ

theorem PreservesAcceptedGuesses.family_subset_at_successor {α C A : V} [IsOrdinal α]
    (h : PreservesAcceptedGuesses (succ α) C A) :
    acceptedGuessFamily (succ α) C A ⊆
      power (structureDomain (C ‘ α)) ×ˢ power (structureDomain (C ‘ α)) := by
  intro p hp
  obtain ⟨β, hβ, hacc, rfl⟩ := (mem_acceptedGuessFamily (succ α) C A p).mp hp
  have hcur := h.family_at_successor (guessedU A C β) (guessedW A C β)
    ((pair_mem_acceptedGuessFamily _ _ _ _ _).mpr ⟨β, hβ, hacc, rfl, rfl⟩)
  exact kpair_mem_iff.mpr ⟨mem_power_iff.mpr hcur.1, mem_power_iff.mpr hcur.2.1⟩

theorem acceptedGuessFamily_successor_data {α C A models : V} [IsOrdinal α]
    (hα : IsInternallyCountable (succ α)) (hC : C ∈ models ^ succ α)
    (hpres : PreservesAcceptedGuesses (succ α) C A) :
    C ‘ α ∈ models ∧ IsInternallyCountable (acceptedGuessFamily (succ α) C A) ∧
      acceptedGuessFamily (succ α) C A ⊆
        power (structureDomain (C ‘ α)) ×ˢ power (structureDomain (C ‘ α)) ∧
      ∀ U W, ⟨U, W⟩ₖ ∈ acceptedGuessFamily (succ α) C A → IsCodedInseparable (C ‘ α) U W :=
  ⟨function_value_mem hC (mem_succ_iff.mpr (Or.inl rfl)), acceptedGuessFamily_countable hα,
    hpres.family_subset_at_successor, hpres.family_at_successor⟩

end ZFVP.Schmerl
