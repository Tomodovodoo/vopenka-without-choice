import ZFVP.SetTheory.NaturalArithmeticLaws
import ZFVP.SetTheory.BoundedNaturals

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem ordinalAdd_one_left_natural {η : V} (hη : η ∈ (ω : V)) :
    ordinalAdd (1 : V) η = succ η :=
  (ordinalAdd_comm_natural (by simp) hη).trans (ordinalAdd_one_natural hη)

theorem ordinal_subset_add_right (α β : V) [IsOrdinal α] [IsOrdinal β] : β ⊆ ordinalAdd α β := by
  apply transfinite_induction (fun β ↦ β ⊆ ordinalAdd α β) (by definability) ?_ (IsOrdinal.toOrdinal β)
  intro β ih x hx
  let := IsOrdinal.of_mem hx
  have hs : x ⊆ ordinalAdd α x := ih (IsOrdinal.toOrdinal x) hx
  exact (mem_ordinalAdd_iff α β.val x).mpr
    (Or.inr ⟨x, hx, mem_succ_iff.mpr (IsOrdinal.subset_iff.mp hs)⟩)

theorem ordinalAdd_one_left_infinite {η : V} [IsOrdinal η] (hη : η ∉ (ω : V)) :
    ordinalAdd (1 : V) η = η := by
  let : IsOrdinal (1 : V) := IsOrdinal.of_mem (show (1 : V) ∈ (ω : V) by simp)
  apply transfinite_induction (fun η ↦ η ∉ (ω : V) → ordinalAdd (1 : V) η = η)
    (by definability) ?_ (IsOrdinal.toOrdinal η) hη
  intro η ih hn
  have hω : (ω : V) ⊆ η.val := by
    rcases IsOrdinal.mem_trichotomy η.val (ω : V) with h | h | h
    · exact False.elim (hn h)
    · exact h ▸ subset_refl _
    · exact IsOrdinal.toIsTransitive.transitive _ h
  apply SetTheory.subset_antisymm ?_ (ordinal_subset_add_right 1 η.val)
  intro x hx
  rcases (mem_ordinalAdd_iff (1 : V) η.val x).mp hx with hx | ⟨ξ, hξ, hx⟩
  · exact hω x (IsOrdinal.toIsTransitive.mem_trans hx (show (1 : V) ∈ (ω : V) by simp))
  · let := IsOrdinal.of_mem hξ
    by_cases hfin : ξ ∈ (ω : V)
    · rw [ordinalAdd_one_left_natural hfin] at hx
      exact hω x (IsOrdinal.toIsTransitive.mem_trans hx (ω_succ_closed (ω_succ_closed hfin)))
    · have he : ordinalAdd (1 : V) ξ = ξ := ih (IsOrdinal.toOrdinal ξ) hξ hfin
      rw [he] at hx
      rcases mem_succ_iff.mp hx with rfl | hx
      · exact hξ
      · exact IsOrdinal.toIsTransitive.mem_trans hx hξ

def sigmaOneOrdinalLeftOneFormula : SetTheorySemisentence 2 :=
  “ξ η. !IsOrdinal.dfn η ∧ ∃ w, !boundedOmegaFormula w ∧
    ((η ∈ w ∧ !boundedSuccFormula ξ η) ∨ (η ∉ w ∧ ξ = η))”

theorem sigmaOneOrdinalLeftOneFormula_sigmaOne : IsSigmaFormula 1 sigmaOneOrdinalLeftOneFormula :=
  .and (.bounded (isOrdinalFormula_bounded.subst _))
    (.exs (.bounded (.and (boundedOmegaFormula_bounded.subst _)
      (.or (.and (.rel _ _) (boundedSuccFormula_bounded.subst _)) (.and (.nrel _ _) (.rel _ _))))))

theorem eval_sigmaOneOrdinalLeftOneFormula (ξ η : V) :
    sigmaOneOrdinalLeftOneFormula.Evalb ![ξ, η] ↔ IsOrdinal η ∧ ξ = ordinalAdd (1 : V) η := by
  simp [sigmaOneOrdinalLeftOneFormula]
  intro hη
  let := hη
  constructor
  · rintro (h | h)
    · exact h.2.trans (ordinalAdd_one_left_natural h.1).symm
    · exact h.2.trans (ordinalAdd_one_left_infinite h.1).symm
  · intro he
    subst ξ
    by_cases hn : η ∈ (ω : V)
    · exact Or.inl ⟨hn, ordinalAdd_one_left_natural hn⟩
    · exact Or.inr ⟨hn, ordinalAdd_one_left_infinite hn⟩

end ZFVP
