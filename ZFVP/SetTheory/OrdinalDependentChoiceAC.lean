import ZFVP.SetTheory.OrdinalDependentChoice
import ZFVP.SetTheory.WellOrderedSelection

/-! Choice is equivalent to dependent choices at every internal ordinal. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem dependentChoiceAt_of_internalChoice (hAC : InternalChoice V)
    (γ : V) [IsOrdinal γ] : InternalDependentChoiceAt γ := by
  intro A R _ hR
  let C : V → V := fun s ↦ {x ∈ A ; ⟨s, x⟩ₖ ∈ R}
  have hC : ℒₛₑₜ-function₁ C := by
    have h : ℒₛₑₜ-relation (fun B s : V ↦ ∀ x, x ∈ B ↔ x ∈ A ∧ ⟨s, x⟩ₖ ∈ R) := by
      definability
    apply Language.Definable.of_iff h
    intro v
    rw [mem_ext_iff]
    simp only [C, mem_sep_iff]
    rfl
  obtain ⟨g, _, _, hg⟩ := choice_for_definable_family hAC (shorterSequences γ A) C hC (by
    intro s hs
    obtain ⟨x, hx, hsx⟩ := hR s hs
    exact ⟨x, mem_sep_iff.mpr ⟨hx, hsx⟩⟩)
  let G : V → V := fun s ↦ g ‘ s
  have hG : ℒₛₑₜ-function₁ G := by unfold G; definability
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
    exact (mem_sep_iff.mp (hg (f ↾ β.val) ((mem_shorterSequences _ _ _).mpr
      ⟨β.val, hβ, hprefix⟩))).1
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
  have hc := (mem_sep_iff.mp (hg (f ↾ β) ((mem_shorterSequences _ _ _).mpr ⟨β, hβ, hprefix⟩))).2
  rwa [hnext β hβ]

theorem internalChoice_of_all_dependentChoiceAt
    (hDC : ∀ γ : V, IsOrdinal γ → InternalDependentChoiceAt γ) : InternalChoice V := by
  apply internalChoice_of_all_wellOrderable
  intro A
  rcases eq_empty_or_isNonempty A with rfl | hA
  · exact ordinal_wellOrderable ∅
  by_contra hbad
  let θ := hartogsNumber A
  let Q : V := {z ∈ shorterSequences θ A ×ˢ A ; kpair.π₂ z ∉ range (kpair.π₁ z)}
  have hQ (s x : V) : ⟨s, x⟩ₖ ∈ Q ↔
      s ∈ shorterSequences θ A ∧ x ∈ A ∧ x ∉ range s := by
    simp only [Q, mem_sep_iff, kpair_mem_iff, kpair.π₁_kpair, kpair.π₂_kpair]
    tauto
  have hserial : ∀ s ∈ shorterSequences θ A, ∃ x ∈ A, ⟨s, x⟩ₖ ∈ Q := by
    intro s hs
    obtain ⟨β, hβ, hsf⟩ := (mem_shorterSequences _ _ _).mp hs
    let := IsOrdinal.of_mem hβ
    have hfresh : ∃ x ∈ A, x ∉ range s := by
      by_contra hn
      have hr : range s = A := SetTheory.subset_antisymm (range_subset_of_mem_function hsf)
        (by intro x hx; by_contra hxr; exact hn ⟨x, hx, hxr⟩)
      exact hbad (wellOrderable_of_surjective_function (ordinal_wellOrderable β) hsf hr)
    obtain ⟨x, hx, hxr⟩ := hfresh
    exact ⟨x, hx, (hQ s x).mpr ⟨hs, hx, hxr⟩⟩
  obtain ⟨f, hf, hstep⟩ := hDC θ inferInstance A Q hA hserial
  let := IsFunction.of_mem hf
  apply not_hartogsNumber_cardLE A
  refine ⟨f, hf, ?_⟩
  intro x y z hx hy
  have hxθ : x ∈ θ := (mem_of_mem_functions hf hx).1
  have hyθ : y ∈ θ := (mem_of_mem_functions hf hy).1
  let := IsOrdinal.of_mem hxθ
  let := IsOrdinal.of_mem hyθ
  rcases IsOrdinal.mem_trichotomy x y with hxy | he | hyx
  · have hn := ((hQ _ _).mp (hstep y hyθ)).2.2
    rw [value_eq_of_kpair_mem hy] at hn
    exact False.elim (hn (mem_range_of_kpair_mem (kpair_mem_restrict_iff.mpr ⟨hx, hxy⟩)))
  · exact he
  · have hn := ((hQ _ _).mp (hstep x hxθ)).2.2
    rw [value_eq_of_kpair_mem hx] at hn
    exact False.elim (hn (mem_range_of_kpair_mem (kpair_mem_restrict_iff.mpr ⟨hy, hyx⟩)))

theorem internalChoice_iff_all_dependentChoiceAt :
    InternalChoice V ↔ ∀ γ : V, IsOrdinal γ → InternalDependentChoiceAt γ :=
  ⟨fun h γ hγ ↦ @dependentChoiceAt_of_internalChoice V _ _ _ h γ hγ,
    internalChoice_of_all_dependentChoiceAt⟩

end ZFVP
