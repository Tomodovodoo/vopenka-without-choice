import ZFVP.SetTheory.InternalChoice
import ZFVP.SetTheory.WellOrderedCardinal
import ZFVP.SetTheory.InverseFunction

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def ordinalImage (f X : V) : V := repl (fun x ↦ f ‘ x) (by definability) X

instance ordinalImage_definable : ℒₛₑₜ-function₂[V] ordinalImage := by
  have h : ℒₛₑₜ-relation₃ (fun Y f X : V ↦ ∀ y, y ∈ Y ↔ ∃ x ∈ X, y = f ‘ x) := by
    definability
  apply Language.Definable.of_iff h
  intro v
  rw [mem_ext_iff]
  simp [ordinalImage, repl_spec]

theorem mem_ordinalImage (f X y : V) : y ∈ ordinalImage f X ↔ ∃ x ∈ X, y = f ‘ x :=
  repl_spec (by definability)

noncomputable def wellOrderSelection (f X : V) : V := (converseGraph f) ‘ (⋂ˢ ordinalImage f X)

instance wellOrderSelection_definable : ℒₛₑₜ-function₂[V] wellOrderSelection := by
  unfold wellOrderSelection
  definability

theorem wellOrderSelection_mem {U α f X : V} [IsOrdinal α] (hf : f ∈ α ^ U)
    (hinj : Injective f) (hX : X ⊆ U) (hn : IsNonempty X) : wellOrderSelection f X ∈ X := by
  obtain ⟨x, hx⟩ := hn.nonempty
  have : IsNonempty (ordinalImage f X) := ⟨f ‘ x, (mem_ordinalImage _ _ _).mpr ⟨x, hx, rfl⟩⟩
  have hm : ⋂ˢ ordinalImage f X ∈ ordinalImage f X := IsOrdinal.sInter_mem (fun y hy ↦ by
    obtain ⟨z, hz, rfl⟩ := (mem_ordinalImage _ _ _).mp hy
    exact IsOrdinal.of_mem (function_value_mem hf (hX z hz)))
  obtain ⟨y, hy, heq⟩ := (mem_ordinalImage _ _ _).mp hm
  unfold wellOrderSelection
  rw [heq, converseGraph_value_value hf hinj (hX y hy)]
  exact hy

theorem choiceFunction_of_wellOrderable_union {A : V} (hU : IsWellOrderable (⋃ˢ A))
    (hn : ∀ X ∈ A, IsNonempty X) : ∃ c ∈ (⋃ˢ A) ^ A, ∀ X ∈ A, c ‘ X ∈ X := by
  obtain ⟨α, hα, f, hf, hinj⟩ := (wellOrderable_iff_cardLE_ordinal _).mp hU
  have : IsOrdinal α := hα
  have hval (X : V) (hX : X ∈ A) : wellOrderSelection f X ∈ X :=
    wellOrderSelection_mem hf hinj (fun x hx ↦ mem_sUnion_iff.mpr ⟨X, hX, hx⟩) (hn X hX)
  let c := definableGraph A (wellOrderSelection f) (by definability)
  refine ⟨c, definableGraph_mem_function_of_mapsTo _ _ _ _ (fun X hX ↦
    mem_sUnion_iff.mpr ⟨X, hX, hval X hX⟩), ?_⟩
  intro X hX
  rw [show c ‘ X = wellOrderSelection f X from value_definableGraph _ _ _ hX]
  exact hval X hX

theorem internalChoice_of_all_wellOrderable (h : ∀ A : V, IsWellOrderable A) : InternalChoice V := by
  intro A hn
  exact choiceFunction_of_wellOrderable_union (h _) hn

theorem models_ac_of_all_wellOrderable (h : ∀ A : V, IsWellOrderable A) : V↓[ℒₛₑₜ] ⊧* 𝗔𝗖 :=
  models_ac_of_internalChoice (internalChoice_of_all_wellOrderable h)

noncomputable def unchosenElements (A g : V) : V := {x ∈ A ; x ∉ range g}

instance unchosenElements_definable : ℒₛₑₜ-function₂[V] unchosenElements := by
  have h : ℒₛₑₜ-relation₃ (fun X A g : V ↦ ∀ x, x ∈ X ↔ x ∈ A ∧ x ∉ range g) := by
    definability
  apply Language.Definable.of_iff h
  intro v
  rw [mem_ext_iff]
  simp [unchosenElements]

noncomputable def wellOrderingStep (A c g : V) : V := by
  classical
  exact if IsNonempty (unchosenElements A g) then c ‘ (unchosenElements A g) else A

instance wellOrderingStep_definable : ℒₛₑₜ-function₃[V] wellOrderingStep := by
  have h : ℒₛₑₜ-relation₄ (fun y A c g : V ↦
    (IsNonempty (unchosenElements A g) ∧ y = c ‘ (unchosenElements A g)) ∨
    (¬IsNonempty (unchosenElements A g) ∧ y = A)) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = wellOrderingStep (v 1) (v 2) (v 3) ↔ _
  unfold wellOrderingStep
  split <;> simp_all

theorem wellOrderable_of_internalChoice (hAC : InternalChoice V) (A : V) : IsWellOrderable A := by
  classical
  let P : V := {X ∈ power A ; IsNonempty X}
  obtain ⟨c, _, hc⟩ := hAC P (fun X hX ↦ (mem_sep_iff.mp hX).2)
  have hchoose (X : V) (hXA : X ⊆ A) (hn : IsNonempty X) : c ‘ X ∈ X :=
    hc X (mem_sep_iff.mpr ⟨mem_power_iff.mpr hXA, hn⟩)
  let F := wellOrderingStep A c
  have hF : ℒₛₑₜ-function₁ F := by unfold F; definability
  let a := Replacement.transfiniteRec F hF
  have ha : ℒₛₑₜ-function₁ a := Replacement.transfiniteRec_definable hF
  let G := fun β ↦ definableGraph β a ha
  have hrec (β : V) [IsOrdinal β] : a β = F (G β) :=
    Replacement.transfiniteRec_spec F hF (IsOrdinal.toOrdinal β)
  have hstep (g : V) (hn : IsNonempty (unchosenElements A g)) :
      F g ∈ A ∧ F g ∉ range g := by
    have hs := hchoose (unchosenElements A g) (fun x hx ↦ (mem_sep_iff.mp hx).1) hn
    have heq : F g = c ‘ (unchosenElements A g) := by simp only [F, wellOrderingStep, hn, ↓reduceIte]
    rw [heq]
    exact mem_sep_iff.mp hs
  have hfresh (β : V) [IsOrdinal β] (hβ : a β ∈ A) : a β ∉ range (G β) := by
    rw [hrec β] at hβ ⊢
    by_cases hn : IsNonempty (unchosenElements A (G β))
    · exact (hstep _ hn).2
    · have heq : F (G β) = A := by simp [F, wellOrderingStep, hn]
      exact False.elim (mem_irrefl A (heq ▸ hβ))
  have hdistinct {β γ : V} [IsOrdinal β] [IsOrdinal γ] (hγ : a γ ∈ A)
      (hlt : β ∈ γ) : a β ≠ a γ := by
    intro heq
    apply hfresh γ hγ
    exact heq ▸ mem_range_of_kpair_mem ((pair_mem_definableGraph_iff γ a ha β (a β)).mpr ⟨hlt, rfl⟩)
  have hinj (δ : V) [IsOrdinal δ] (hδ : ∀ β ∈ δ, a β ∈ A) : Injective (G δ) := by
    intro β γ z hβ hγ
    obtain ⟨hβδ, hzβ⟩ := (pair_mem_definableGraph_iff δ a ha β z).mp hβ
    obtain ⟨hγδ, hzγ⟩ := (pair_mem_definableGraph_iff δ a ha γ z).mp hγ
    have : IsOrdinal β := IsOrdinal.of_mem hβδ
    have : IsOrdinal γ := IsOrdinal.of_mem hγδ
    have heq : a β = a γ := hzβ.symm.trans hzγ
    rcases IsOrdinal.mem_trichotomy β γ with hlt | he | hgt
    · exact False.elim (hdistinct (hδ γ hγδ) hlt heq)
    · exact he
    · exact False.elim (hdistinct (hδ β hβδ) hgt heq.symm)
  have hex : ∃ β : V, IsOrdinal β ∧ β ∈ hartogsNumber A ∧ a β ∉ A := by
    by_contra hn
    have hall : ∀ β ∈ hartogsNumber A, a β ∈ A := by
      intro β hβ
      by_contra hbad
      exact hn ⟨β, IsOrdinal.of_mem hβ, hβ, hbad⟩
    exact not_hartogsNumber_cardLE A ⟨G (hartogsNumber A),
      definableGraph_mem_function_of_mapsTo _ _ _ _ hall, hinj _ hall⟩
  obtain ⟨β, hβ, _⟩ := leastOrdinal_existsUnique
    (fun β ↦ β ∈ hartogsNumber A ∧ a β ∉ A) (by definability) hex
  have : IsOrdinal β := hβ.1
  have hbefore : ∀ γ ∈ β, a γ ∈ A := by
    intro γ hγ
    have : IsOrdinal γ := IsOrdinal.of_mem hγ
    by_contra hbad
    have hγH := IsOrdinal.toIsTransitive.transitive _ hβ.2.1.1 γ hγ
    exact mem_irrefl γ (hβ.2.2 γ inferInstance ⟨hγH, hbad⟩ γ hγ)
  have hg : G β ∈ A ^ β := definableGraph_mem_function_of_mapsTo _ _ _ _ hbefore
  have hr : range (G β) = A := by
    apply SetTheory.subset_antisymm (range_subset_of_mem_function hg)
    intro x hx
    by_contra hn
    have hn' : IsNonempty (unchosenElements A (G β)) := ⟨x, mem_sep_iff.mpr ⟨hx, hn⟩⟩
    exact hβ.2.1.2 ((hrec β).symm ▸ (hstep _ hn').1)
  have hcon := converseGraph_mem_function hg (hinj β hbefore)
  rw [hr] at hcon
  exact (wellOrderable_iff_cardLE_ordinal A).mpr ⟨β, inferInstance,
    converseGraph (G β), hcon, converseGraph_injective _⟩

theorem internalChoice_iff_all_wellOrderable : InternalChoice V ↔ ∀ A : V, IsWellOrderable A :=
  ⟨wellOrderable_of_internalChoice, internalChoice_of_all_wellOrderable⟩

theorem models_ac_iff_all_wellOrderable : V↓[ℒₛₑₜ] ⊧* 𝗔𝗖 ↔ ∀ A : V, IsWellOrderable A :=
  internalChoice_iff_models_ac.symm.trans internalChoice_iff_all_wellOrderable

end ZFVP


