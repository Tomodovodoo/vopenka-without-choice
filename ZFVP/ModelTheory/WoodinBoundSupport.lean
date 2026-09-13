import ZFVP.ModelTheory.WoodinBoundCoherence
import ZFVP.ModelTheory.WoodinStageSections

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {δ θ ξ i p f : V} [IsOrdinal θ]
  (hs : ∀ j ∈ θ, IsWoodinIteration δ (succ j) (kpair.π₁ (woodinIterationRec j))
    (kpair.π₂ (woodinIterationRec j))) (hi : i ∈ θ)
  (hmem : ∀ j ∈ θ, woodinQuotientBoundRec ξ i p f j ∈
    (forcingCodeP (woodinIterationPrefix θ)) ‘ j)
include hs hi hmem

theorem woodinQuotientBoundHistory_eq_section {j b : V} [IsOrdinal j]
    (hj : j ⊆ θ) (hb : b ∈ j)
    (hupper : ∀ l ∈ j, b ⊆ l → woodinQuotientBoundRec ξ i p f l =
      ((forcingCodeE (woodinIterationPrefix θ)) ‘ ⟨b, l⟩ₖ) ‘ (woodinQuotientBoundRec ξ i p f b)) :
    woodinQuotientBoundHistory ξ i p f j =
      forcingSectionThread j (forcingCodeπ (woodinIterationPrefix j))
        (forcingCodeE (woodinIterationPrefix j)) b (woodinQuotientBoundRec ξ i p f b) := by
  classical
  let := IsOrdinal.of_mem hb
  let := (woodinQuotientBoundHistory_table ξ i p f j).function
  let : IsFunction (forcingSectionThread j (forcingCodeπ (woodinIterationPrefix j))
      (forcingCodeE (woodinIterationPrefix j)) b (woodinQuotientBoundRec ξ i p f b)) := by
    unfold forcingSectionThread
    infer_instance
  have hc := (woodinIterationPrefix_of_stages hs).code
  have hcj := (woodinIterationPrefix_of_stages (fun l hl ↦ hs l (hj l hl))).code
  have he := woodinIterationPrefix_extends hj
  apply functions_eq_of_domain_values
  · rw [(woodinQuotientBoundHistory_table ξ i p f j).domain_eq]
    simp only [forcingSectionThread, domain_definableGraph]
  · intro l hl
    rw [(woodinQuotientBoundHistory_table ξ i p f j).domain_eq] at hl
    let := IsOrdinal.of_mem hl
    rw [woodinQuotientBoundHistory_value hl, forcingSectionThread_value hl]
    unfold forcingSectionValue
    by_cases hlb : l ∈ b
    · rw [ite_eq_left hlb,
        hcj.tableπ.value_of_subset hc.tableπ he.subπ (mem_prod_iff.mpr ⟨l, hl, b, hb, rfl⟩)]
      exact (woodinQuotientBoundRec_projects_of_membership hs hi hmem b (hj b hb) l
        (mem_succ_iff.mpr (Or.inr hlb))).symm
    · rw [ite_eq_right hlb,
        hcj.tableE.value_of_subset hc.tableE he.subE (mem_prod_iff.mpr ⟨b, hb, l, hl, rfl⟩)]
      apply hupper l hl
      rcases IsOrdinal.mem_trichotomy b l with hbl | rfl | hlb'
      · exact IsOrdinal.toIsTransitive.transitive _ hbl
      · exact subset_refl _
      · exact False.elim (hlb hlb')

theorem woodinQuotientBoundRec_section_of_empty_tails {b : V}
    (hb : b ∈ θ) (hib : i ⊆ b)
    (hS : ∀ k, succ k ∈ θ → b ⊆ k → woodinBoundSuccessorTail ξ i p f k = ∅)
    (hI : ∀ j ∈ θ, b ∈ j → j ≠ succ (⋃ˢ j) →
      ¬IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix j)) →
        woodinBoundInverseTail ξ i p f j = ∅) :
    ∀ j ∈ θ, b ⊆ j → woodinQuotientBoundRec ξ i p f j =
      ((forcingCodeE (woodinIterationPrefix θ)) ‘ ⟨b, j⟩ₖ) ‘ (woodinQuotientBoundRec ξ i p f b) := by
  let := IsOrdinal.of_mem hi
  let := IsOrdinal.of_mem hb
  have hc := (woodinIterationPrefix_of_stages hs).code
  have hall := transfinite_induction
    (fun j : V ↦ j ∈ θ → b ⊆ j → woodinQuotientBoundRec ξ i p f j =
      ((forcingCodeE (woodinIterationPrefix θ)) ‘ ⟨b, j⟩ₖ) ‘ (woodinQuotientBoundRec ξ i p f b))
    (by definability) ?_
  · intro j hj hbj
    let := IsOrdinal.of_mem hj
    exact hall (IsOrdinal.toOrdinal j) hj hbj
  intro j ih hj hbj
  rcases IsOrdinal.subset_iff.mp hbj with heq | hbj
  · rw [← heq]
    exact (hc.system.split.secId b hb _ (hmem b hb)).symm
  have hij : i ∈ (j : V) := ordinal_mem_of_subset_mem hib hbj
  have hsub : (j : V) ⊆ θ := IsOrdinal.toIsTransitive.transitive _ hj
  have hupper : ∀ l ∈ (j : V), b ⊆ l → woodinQuotientBoundRec ξ i p f l =
      ((forcingCodeE (woodinIterationPrefix θ)) ‘ ⟨b, l⟩ₖ) ‘ (woodinQuotientBoundRec ξ i p f b) := by
    intro l hl hbl
    let := IsOrdinal.of_mem hl
    exact ih (IsOrdinal.toOrdinal l) hl (hsub l hl) hbl
  by_cases hsucc : (j : V) = succ (⋃ˢ (j : V))
  · have hk : ⋃ˢ (j : V) ∈ (j : V) :=
      (congrArg (fun x : V ↦ (⋃ˢ (j : V)) ∈ x) hsucc).mpr (mem_succ_self (⋃ˢ (j : V)))
    let := IsOrdinal.of_mem hk
    have hbk : b ⊆ ⋃ˢ (j : V) := IsOrdinal.subset_iff.mpr (mem_succ_iff.mp (hsucc ▸ hbj))
    have hprev := hupper _ hk hbk
    have hh : woodinQuotientBoundRec ξ i p f (succ (⋃ˢ (j : V))) =
        ((forcingCodeE (woodinIterationPrefix θ)) ‘ ⟨b, succ (⋃ˢ (j : V))⟩ₖ) ‘
          (woodinQuotientBoundRec ξ i p f b) := by
      rw [woodinQuotientBoundRec_successor (hsucc ▸ hij),
        woodinIterationPrefix_section_successor hs (hsucc ▸ hj) (hsucc ▸ hbj) (hmem b hb),
        hS _ (hsucc ▸ hj) hbk, hprev]
    rwa [← hsucc] at hh
  · have hhistory := woodinQuotientBoundHistory_eq_section hs hi hmem hsub hbj hupper
    by_cases hinac : IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix (j : V)))
    · rw [woodinQuotientBoundRec_direct hij hsucc hinac,
        woodinIterationPrefix_section_direct hs hj hbj hsucc hinac (hmem b hb)]
      exact hhistory
    · rw [woodinQuotientBoundRec_inverse hij hsucc hinac,
        woodinIterationPrefix_section_inverse hs hj hbj hsucc hinac (hmem b hb), hI j hj hbj hsucc hinac,
        hhistory]

theorem woodinQuotientBoundHistory_mem_direct_of_empty_tails {b : V}
    (hb : b ∈ θ) (hib : i ⊆ b)
    (hS : ∀ k, succ k ∈ θ → b ⊆ k → woodinBoundSuccessorTail ξ i p f k = ∅)
    (hI : ∀ j ∈ θ, b ∈ j → j ≠ succ (⋃ˢ j) →
      ¬IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix j)) →
        woodinBoundInverseTail ξ i p f j = ∅) :
    woodinQuotientBoundHistory ξ i p f θ ∈
      forcingDirectLimit θ (forcingCodeP (woodinIterationPrefix θ))
        (forcingCodeπ (woodinIterationPrefix θ)) (forcingCodeE (woodinIterationPrefix θ))
        (forcingCodeUniverse (woodinIterationPrefix θ)) := by
  apply (mem_forcingDirectLimit_iff _ _ _ _ _ _).mpr
  refine ⟨woodinQuotientBoundHistory_mem_inverse_of_membership hs hi hmem, b, hb, ?_⟩
  intro j hj hbj
  rw [woodinQuotientBoundHistory_value hj, woodinQuotientBoundHistory_value hb]
  exact woodinQuotientBoundRec_section_of_empty_tails hs hi hmem hb hib hS hI j hj hbj

end ZFVP
