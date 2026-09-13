import ZFVP.ModelTheory.DirectedElementaryUnion
import ZFVP.Syntax.MembershipSwap

/-! Reflecting witnesses and Collection through a transitive elementary submodel. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace IsElementaryInclusion

theorem exists_second_iff {A B n φ b x : V} (h : IsElementaryInclusion A B)
    (hn : n ∈ (ω : V)) (hφ : IsMembershipFormulaCode (succ (succ n)) φ)
    (hb : b ∈ A ^ n) (hx : x ∈ A) :
    (∃ y ∈ A, MembershipSatisfies A (succ (succ n)) φ
      (assignmentPrepend (succ n) (assignmentPrepend n b y) x)) ↔
    (∃ y ∈ B, MembershipSatisfies B (succ (succ n)) φ
      (assignmentPrepend (succ n) (assignmentPrepend n b y) x)) := by
  have hφ' := (mem_formulaSet_iff _ _ _ _).mpr hφ
  have hswap := swapMembershipFormula_mem hn hφ'
  have he := h.satisfaction_iff (ω_succ_closed hn)
    ((mem_formulaSet_iff _ _ _ _).mp (formulaSet_quantifiers membershipLanguageCode_valid
      (ω_succ_closed hn) hswap).2) (assignmentPrepend_mem_function hn hb hx)
  have hbB := mem_function_of_mem_function_of_subset hb h.subset
  rw [membershipSatisfies_exists (ω_succ_closed hn) hswap (assignmentPrepend_mem_function hn hb hx),
    membershipSatisfies_exists (ω_succ_closed hn) hswap
      (assignmentPrepend_mem_function hn hbB (h.subset _ hx))] at he
  constructor
  · rintro ⟨y, hy, hxy⟩
    obtain ⟨z, hz, hxz⟩ := he.mp ⟨y, hy,
      (membershipSatisfies_swap h.source_nonempty hn hφ' hb hx hy).mpr hxy⟩
    exact ⟨z, hz, (membershipSatisfies_swap h.target_nonempty hn hφ' hbB (h.subset _ hx) hz).mp hxz⟩
  · rintro ⟨y, hy, hxy⟩
    obtain ⟨z, hz, hxz⟩ := he.mpr ⟨y, hy,
      (membershipSatisfies_swap h.target_nonempty hn hφ' hbB (h.subset _ hx) hy).mpr hxy⟩
    exact ⟨z, hz, (membershipSatisfies_swap h.source_nonempty hn hφ' hb hx hz).mp hxz⟩

theorem collection_instance {A B n φ b a : V} [IsTransitive A]
    (h : IsElementaryInclusion A B) (hcol : InternalCollection A)
    (hn : n ∈ (ω : V)) (hφ : IsMembershipFormulaCode (succ (succ n)) φ)
    (hb : b ∈ A ^ n) (ha : a ∈ A)
    (htotal : ∀ x ∈ B, x ∈ a → ∃ y ∈ B, MembershipSatisfies B (succ (succ n)) φ
      (assignmentPrepend (succ n) (assignmentPrepend n b y) x)) :
    ∃ c ∈ A, ∀ x ∈ B, x ∈ a → ∃ y ∈ B, y ∈ c ∧
      MembershipSatisfies B (succ (succ n)) φ
        (assignmentPrepend (succ n) (assignmentPrepend n b y) x) := by
  have htA : ∀ x ∈ A, x ∈ a → ∃ y ∈ A, MembershipSatisfies A (succ (succ n)) φ
      (assignmentPrepend (succ n) (assignmentPrepend n b y) x) := by
    intro x hx hxa
    exact (h.exists_second_iff hn hφ hb hx).mpr (htotal x (h.subset _ hx) hxa)
  obtain ⟨c, hc, hw⟩ := hcol n hn φ hφ b hb a ha htA
  refine ⟨c, hc, ?_⟩
  intro x _ hxa
  have hx : x ∈ A := (inferInstance : IsTransitive A).mem_trans hxa ha
  obtain ⟨y, hy, hyc, hxy⟩ := hw x hx hxa
  exact ⟨y, h.subset _ hy, hyc, (h.satisfaction_iff (ω_succ_closed (ω_succ_closed hn)) hφ
    (assignmentPrepend_mem_function (ω_succ_closed hn) (assignmentPrepend_mem_function hn hb hy) hx)).mp hxy⟩

end IsElementaryInclusion

theorem rank_internalReplacement_of_collection {θ : V} [IsOrdinal θ]
    (hs : ∀ β ∈ θ, succ β ∈ θ) (hcol : InternalCollection (hierarchy θ)) :
    InternalReplacement (hierarchy θ) := by
  intro n hn φ hφ b hb a ha htotal
  have ht : ∀ x ∈ hierarchy θ, x ∈ a → ∃ y ∈ hierarchy θ,
      MembershipSatisfies (hierarchy θ) (succ (succ n)) φ
        (assignmentPrepend (succ n) (assignmentPrepend n b y) x) := by
    intro x hx hxa
    obtain ⟨y, hy, _⟩ := htotal x hx hxa
    exact ⟨y, hy⟩
  obtain ⟨c, hc, hw⟩ := hcol n hn φ hφ b hb a ha ht
  let d := {y ∈ c ; ∃ x ∈ hierarchy θ, x ∈ a ∧
    MembershipSatisfies (hierarchy θ) (succ (succ n)) φ
      (assignmentPrepend (succ n) (assignmentPrepend n b y) x)}
  refine ⟨d, subset_mem_hierarchy_limit hs hc (show d ⊆ c from sep_subset), ?_⟩
  intro y hy
  dsimp only [d]
  rw [mem_sep_iff]
  constructor
  · exact And.right
  · intro hxy
    obtain ⟨x, hx, hxa, hxy'⟩ := hxy
    obtain ⟨z, hz, hzc, hxz⟩ := hw x hx hxa
    have hyz : y = z := (htotal x hx hxa).unique ⟨hy, hxy'⟩ ⟨hz, hxz⟩
    exact ⟨hyz.symm ▸ hzc, x, hx, hxa, hxy'⟩

end ZFVP
