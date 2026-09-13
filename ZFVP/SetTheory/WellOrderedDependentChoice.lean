import ZFVP.SetTheory.DependentChoicePaths
import ZFVP.SetTheory.WellOrderingChoice

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem dependentChoicePath_of_selection {γ A R : V} [IsOrdinal γ]
    (G : V → V) (hG : ℒₛₑₜ-function₁ G)
    (hnextValue : ∀ s ∈ shorterSequences γ A, G s ∈ A ∧ ⟨s, G s⟩ₖ ∈ R) :
    ∃ f, IsDependentChoicePath A R γ f := by
  obtain ⟨f, hf⟩ := Replacement.attempt_function_exists G hG (IsOrdinal.toOrdinal γ)
  change IsAttempt G γ f at hf
  let := hf.2.1
  have hnext (β : V) (hβ : β ∈ γ) : f ‘ β = G (f ↾ β) :=
    (hf.2.2.2 β hβ (f ‘ β)).mp (kpair_value_mem (hf.2.2.1.symm ▸ hβ))
  have hvalues : ∀ β : Ordinal V, β.val ∈ γ → f ‘ β.val ∈ A := by
    apply transfinite_induction (fun β ↦ β ∈ γ → f ‘ β ∈ A) (by definability)
    intro β ih hβ
    have hprefix : f ↾ β.val ∈ A ^ β.val := restrict_mem_function_of_values
      (by rw [hf.2.2.1]; exact IsOrdinal.toIsTransitive.transitive _ hβ) (by
        intro ξ hξ
        let := IsOrdinal.of_mem hξ
        exact ih (IsOrdinal.toOrdinal ξ) hξ (IsOrdinal.toIsTransitive.mem_trans hξ hβ))
    rw [hnext β hβ]
    exact (hnextValue (f ↾ β.val) ((mem_shorterSequences _ _ _).mpr ⟨β.val, hβ, hprefix⟩)).1
  have hfunc : f ∈ A ^ γ := mem_function.intro
    (by
      intro p hp
      obtain ⟨β, x, rfl⟩ := IsFunction.mem_eq_kpair hp
      have hβ : β ∈ γ := hf.2.2.1 ▸ mem_domain_of_kpair_mem hp
      let := IsOrdinal.of_mem hβ
      exact kpair_mem_iff.mpr ⟨hβ, (value_eq_of_kpair_mem hp) ▸
        hvalues (IsOrdinal.toOrdinal β) hβ⟩)
    (by
      intro β hβ
      exact ⟨f ‘ β, kpair_value_mem (hf.2.2.1.symm ▸ hβ),
        fun x hx ↦ (value_eq_of_kpair_mem hx).symm⟩)
  refine ⟨f, hfunc, ?_⟩
  intro β hβ
  have hprefix := function_restrict_mem hfunc (IsOrdinal.toIsTransitive.transitive _ hβ)
  have hc := (hnextValue (f ↾ β) ((mem_shorterSequences _ _ _).mpr ⟨β, hβ, hprefix⟩)).2
  rwa [hnext β hβ]

theorem dependentChoicePath_of_wellOrderable {γ A R : V} [IsOrdinal γ]
    (hA : IsWellOrderable A)
    (hserial : ∀ s ∈ shorterSequences γ A, ∃ x ∈ A, ⟨s, x⟩ₖ ∈ R) :
    ∃ f, IsDependentChoicePath A R γ f := by
  obtain ⟨α, hα, w, hw, hinj⟩ := (wellOrderable_iff_cardLE_ordinal A).mp hA
  let := hα
  let C : V → V := fun s ↦ {x ∈ A ; ⟨s, x⟩ₖ ∈ R}
  have hC : ℒₛₑₜ-function₁ C := by
    have h : ℒₛₑₜ-relation (fun B s : V ↦ ∀ x, x ∈ B ↔ x ∈ A ∧ ⟨s, x⟩ₖ ∈ R) := by definability
    apply Language.Definable.of_iff h
    intro v
    rw [mem_ext_iff]
    simp only [C, mem_sep_iff]
    rfl
  let G : V → V := fun s ↦ wellOrderSelection w (C s)
  have hG : ℒₛₑₜ-function₁ G := by unfold G; definability
  apply dependentChoicePath_of_selection G hG
  intro s hs
  obtain ⟨x, hx, hsx⟩ := hserial s hs
  exact mem_sep_iff.mp (wellOrderSelection_mem hw hinj
    (fun _ h ↦ (mem_sep_iff.mp h).1) ⟨x, mem_sep_iff.mpr ⟨hx, hsx⟩⟩)

end ZFVP
