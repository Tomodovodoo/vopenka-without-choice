import ZFVP.ModelTheory.SchmerlInternalCarrierAgreementClub
import ZFVP.ModelTheory.SchmerlInternalCodedHullClosure

/-! An actual club closed under a countable family of operations on all
internally finite tuples. No standardness assumption on omega is used. -/

set_option autoImplicit false

namespace ZFVP.Schmerl
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem finiteSequence_bounded_in_limit {α b : V} (hα : IsLimitOrdinal α)
    (hb : b ∈ finiteSequences α) : ∃ β ∈ α, b ∈ finiteSequences β := by
  let : IsOrdinal α := hα.1
  have hzero : (0 : V) ∈ α :=
    IsOrdinal.empty_mem_iff_nonempty.mpr (ne_empty_iff_isNonempty.mp hα.2.1)
  have hsucc : ∀ β ∈ α, succ β ∈ α := by
    intro β hβ
    let : IsOrdinal β := IsOrdinal.of_mem hβ
    rcases IsOrdinal.mem_trichotomy (succ β) α with hs | he | hs
    · exact hs
    · exact False.elim (hα.2.2 ⟨β, he.symm⟩)
    · rcases mem_succ_iff.mp hs with he | hs
      · exact False.elim (mem_irrefl α (he ▸ hβ))
      · exact False.elim (mem_asymm hβ hs)
  obtain ⟨n, hn, hbn⟩ := (mem_finiteSequences_iff α b).mp hb
  obtain ⟨β, hβ, hbound⟩ := finite_map_bounded α hzero hsucc n hn b hbn
  let := IsFunction.of_mem hbn
  have hr : range b ⊆ β := by
    intro x hx
    obtain ⟨i, hix⟩ := mem_range_iff.mp hx
    have hi : i ∈ n := (mem_of_mem_functions hbn hix).1
    exact value_eq_of_kpair_mem hix ▸ hbound i hi
  refine ⟨β, hβ, (mem_finiteSequences_iff β b).mpr ⟨n, hn, ?_⟩⟩
  simpa only [domain_eq_of_mem_function hbn] using
    mem_function_of_mem_function_of_subset (IsFunction.mem_function b) hr

noncomputable def finitaryOperationValues (I g β : V) : V :=
  repl (fun p ↦ g ‘ p) (by definability) (I ×ˢ finiteSequences β)

theorem mem_finitaryOperationValues (I g β x : V) :
    x ∈ finitaryOperationValues I g β ↔
      ∃ i ∈ I, ∃ b ∈ finiteSequences β, x = g ‘ ⟨i, b⟩ₖ := by
  simp only [finitaryOperationValues, repl_spec, mem_prod_iff]
  constructor
  · rintro ⟨p, ⟨i, hi, b, hb, rfl⟩, he⟩
    exact ⟨i, hi, b, hb, he⟩
  · rintro ⟨i, hi, b, hb, rfl⟩
    exact ⟨⟨i, b⟩ₖ, ⟨i, hi, b, hb, rfl⟩, rfl⟩

instance finitaryOperationValues_definable : ℒₛₑₜ-function₃[V] finitaryOperationValues := by
  have hh : ℒₛₑₜ-relation₄[V] (fun X I g β ↦ ∀ x, x ∈ X ↔
      ∃ i ∈ I, ∃ b ∈ finiteSequences β, x = g ‘ ⟨i, b⟩ₖ) := by definability
  apply Language.Definable.of_iff hh
  intro v
  rw [mem_ext_iff]
  simp only [mem_finitaryOperationValues]
  rfl

theorem finitaryOperationValues_countable (hAC : InternalChoice V) {I g β : V}
    (hI : IsInternallyCountable I) (hβ : IsInternallyCountable β) :
    IsInternallyCountable (finitaryOperationValues I g β) :=
  internallyCountable_repl _ _
    ((prod_cardLE_prod hI (internallyCountable_finiteSequences hAC hβ)).trans omega_prod_cardLE_omega)

theorem finitaryOperationValues_subset {κ I g β : V}
    (hg : g ∈ κ ^ (I ×ˢ finiteSequences κ)) (hβ : β ⊆ κ) :
    finitaryOperationValues I g β ⊆ κ := by
  intro x hx
  obtain ⟨i, hi, b, hb, rfl⟩ := (mem_finitaryOperationValues I g β x).mp hx
  obtain ⟨n, hn, hbn⟩ := (mem_finiteSequences_iff β b).mp hb
  exact function_value_mem hg (kpair_mem_iff.mpr ⟨hi,
    (mem_finiteSequences_iff κ b).mpr ⟨n, hn, mem_function_of_mem_function_of_subset hbn hβ⟩⟩)

noncomputable def finitaryClosureBound (I g β : V) : V := succ (⋃ˢ finitaryOperationValues I g β)

instance finitaryClosureBound_definable : ℒₛₑₜ-function₃[V] finitaryClosureBound := by
  unfold finitaryClosureBound
  definability

noncomputable def finitaryClosureBoundGraph (κ I g : V) : V :=
  definableGraph κ (finitaryClosureBound I g) (by definability)

instance finitaryClosureBoundGraph_definable : ℒₛₑₜ-function₃[V] finitaryClosureBoundGraph := by
  have hh : ℒₛₑₜ-relation₄[V] (fun f κ I g ↦ ∀ p, p ∈ f ↔
      ∃ β ∈ κ, p = ⟨β, finitaryClosureBound I g β⟩ₖ) := by definability
  apply Language.Definable.of_iff hh
  intro v
  rw [mem_ext_iff]
  simp only [finitaryClosureBoundGraph, mem_definableGraph_iff]
  rfl

theorem finitaryClosureBoundGraph_value {κ I g β : V} (hβ : β ∈ κ) :
    (finitaryClosureBoundGraph κ I g) ‘ β = finitaryClosureBound I g β :=
  value_definableGraph _ _ _ hβ

theorem hartogsOmega_finitaryClosureBound (hAC : InternalChoice V) {I g β : V}
    (hI : IsInternallyCountable I)
    (hg : g ∈ hartogsNumber (ω : V) ^ (I ×ˢ finiteSequences (hartogsNumber (ω : V))))
    (hβ : β ∈ hartogsNumber (ω : V)) :
    finitaryClosureBound I g β ∈ hartogsNumber (ω : V) ∧
      ∀ i ∈ I, ∀ b ∈ finiteSequences β, g ‘ ⟨i, b⟩ₖ ∈ finitaryClosureBound I g β := by
  have hs := hartogsOmega_countable_strict_bound hAC
    (finitaryOperationValues_countable hAC hI (countable_of_mem_hartogs_omega hβ))
    (finitaryOperationValues_subset hg (IsTransitive.transitive _ hβ))
  refine ⟨hs.1, ?_⟩
  intro i hi b hb
  exact hs.2 _ ((mem_finitaryOperationValues I g β _).mpr ⟨i, hi, b, hb, rfl⟩)

theorem hartogsOmega_finitaryClosureBoundGraph_mem (hAC : InternalChoice V) {I g : V}
    (hI : IsInternallyCountable I)
    (hg : g ∈ hartogsNumber (ω : V) ^ (I ×ˢ finiteSequences (hartogsNumber (ω : V)))) :
    finitaryClosureBoundGraph (hartogsNumber (ω : V)) I g ∈
      hartogsNumber (ω : V) ^ hartogsNumber (ω : V) :=
  definableGraph_mem_function_of_mapsTo _ _ _ _ (fun _ hβ ↦ (hartogsOmega_finitaryClosureBound hAC hI hg hβ).1)

noncomputable def finitaryClosureClub (κ I g : V) : V :=
  functionClosureClub κ (finitaryClosureBoundGraph κ I g)

instance finitaryClosureClub_definable : ℒₛₑₜ-function₃[V] finitaryClosureClub := by
  unfold finitaryClosureClub
  definability

theorem hartogsOmega_finitaryClosureClub (hAC : InternalChoice V) {I g : V}
    (hI : IsInternallyCountable I)
    (hg : g ∈ hartogsNumber (ω : V) ^ (I ×ˢ finiteSequences (hartogsNumber (ω : V)))) :
    IsClubIn (finitaryClosureClub (hartogsNumber (ω : V)) I g) (hartogsNumber (ω : V)) :=
  hartogsOmega_functionClosureClub hAC (hartogsOmega_finitaryClosureBoundGraph_mem hAC hI hg)

theorem hartogsOmega_finitaryClosureClub_closed (hAC : InternalChoice V) {I g α : V}
    (hI : IsInternallyCountable I)
    (hg : g ∈ hartogsNumber (ω : V) ^ (I ×ˢ finiteSequences (hartogsNumber (ω : V))))
    (hα : α ∈ finitaryClosureClub (hartogsNumber (ω : V)) I g) :
    IsLimitOrdinal α ∧ ∀ i ∈ I, ∀ b ∈ finiteSequences α, g ‘ ⟨i, b⟩ₖ ∈ α := by
  obtain ⟨hακ, hlim, hclosed⟩ := (mem_functionClosureClub _ _ _).mp hα
  let : IsOrdinal α := hlim.1
  refine ⟨hlim, ?_⟩
  intro i hi b hb
  obtain ⟨β, hβα, hbβ⟩ := finiteSequence_bounded_in_limit hlim hb
  have hβκ := IsOrdinal.toIsTransitive.mem_trans hβα hακ
  have hv := (hartogsOmega_finitaryClosureBound hAC hI hg hβκ).2 i hi b hbβ
  have hc := hclosed β hβα
  rw [finitaryClosureBoundGraph_value hβκ] at hc
  exact IsOrdinal.toIsTransitive.mem_trans hv hc

theorem exists_hartogsOmega_finitaryClosureClub (hAC : InternalChoice V) {I g : V}
    (hI : IsInternallyCountable I)
    (hg : g ∈ hartogsNumber (ω : V) ^ (I ×ˢ finiteSequences (hartogsNumber (ω : V)))) :
    ∃ E : V, IsClubIn E (hartogsNumber (ω : V)) ∧
      ∀ α ∈ E, IsLimitOrdinal α ∧ ∀ i ∈ I, ∀ b ∈ finiteSequences α, g ‘ ⟨i, b⟩ₖ ∈ α :=
  ⟨finitaryClosureClub (hartogsNumber (ω : V)) I g, hartogsOmega_finitaryClosureClub hAC hI hg,
    fun _ hα ↦ hartogsOmega_finitaryClosureClub_closed hAC hI hg hα⟩

end ZFVP.Schmerl
