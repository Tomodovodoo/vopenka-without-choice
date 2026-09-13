import ZFVP.SetTheory.BinaryClosedImages
import ZFVP.SetTheory.BinaryFibers
import ZFVP.SetTheory.PerfectTreeBranches

/-! A perfect binary tree has a nonempty perfect image on the real line. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem perfectTree_three_branches {T s : V} (hT : IsPerfectTree T) (hs : s ∈ T) :
    ∃ c ∈ treeBody T, ∃ d ∈ treeBody T, ∃ e ∈ treeBody T,
      s ⊆ c ∧ s ⊆ d ∧ s ⊆ e ∧ c ≠ d ∧ c ≠ e ∧ d ≠ e := by
  obtain ⟨u, hu, v, hv, hsu, hsv, huv⟩ := hT.2.2 s hs
  obtain ⟨p, hp, q, hq, hup, huq, hpq⟩ := hT.2.2 u hu
  obtain ⟨c, hc, hpc⟩ := perfectTree_branch_through hT hp
  obtain ⟨d, hd, hqd⟩ := perfectTree_branch_through hT hq
  obtain ⟨e, he, hve⟩ := perfectTree_branch_through hT hv
  have huc := subset_trans hup hpc
  have hud := subset_trans huq hqd
  have : IsFunction c := IsFunction.of_mem (treeBody_subset_cantorSpace T c hc)
  have : IsFunction d := IsFunction.of_mem (treeBody_subset_cantorSpace T d hd)
  have : IsFunction e := IsFunction.of_mem (treeBody_subset_cantorSpace T e he)
  have : IsFunction u := binarySequence_isFunction (hT.1.1 u hu)
  have : IsFunction v := binarySequence_isFunction (hT.1.1 v hv)
  have : IsFunction p := binarySequence_isFunction (hT.1.1 p hp)
  have : IsFunction q := binarySequence_isFunction (hT.1.1 q hq)
  refine ⟨c, hc, d, hd, e, he, subset_trans hsu huc, subset_trans hsu hud,
    subset_trans hsv hve, ?_, ?_, ?_⟩
  · intro hcd
    exact not_incompatible_of_subset_subset hpc (hcd ▸ hqd) hpq
  · intro hce
    exact not_incompatible_of_subset_subset huc (hce ▸ hve) huv
  · intro hde
    exact not_incompatible_of_subset_subset hud (hde ▸ hve) huv

theorem binaryPerfectImage_no_isolated {T x a b : V} (hT : IsPerfectTree T)
    (hx : x ∈ binaryImage (treeBody T)) (ha : a ∈ internalRationals V)
    (hb : b ∈ internalRationals V) (hxi : x ∈ realInterval a b) :
    ∃ y ∈ binaryImage (treeBody T), y ∈ realInterval a b ∧ y ≠ x := by
  obtain ⟨c, hc, rfl⟩ := (mem_binaryImage_iff _ _).mp hx
  have hcC := treeBody_subset_cantorSpace T c hc
  obtain ⟨n, hn, hlo, hup⟩ := binaryPrefixEnds_inside hcC ha hb hxi
  have hsT := ((mem_treeBody_iff _ _).mp hc).2 n hn
  obtain ⟨d, hd, e, he, f, hf, hsd, hse, hsf, hde, hdf, hef⟩ := perfectTree_three_branches hT hsT
  have hdC := treeBody_subset_cantorSpace T d hd
  have heC := treeBody_subset_cantorSpace T e he
  have hfC := treeBody_subset_cantorSpace T f hf
  by_cases hdne : binaryReal d ≠ binaryReal c
  · exact ⟨binaryReal d, (mem_binaryImage_iff _ _).mpr ⟨d, hd, rfl⟩,
      binaryReal_interval_of_prefix hcC hdC hn ha hb hlo hup hsd, hdne⟩
  by_cases hene : binaryReal e ≠ binaryReal c
  · exact ⟨binaryReal e, (mem_binaryImage_iff _ _).mpr ⟨e, he, rfl⟩,
      binaryReal_interval_of_prefix hcC heC hn ha hb hlo hup hse, hene⟩
  have hfne : binaryReal f ≠ binaryReal c := by
    intro heq
    rcases binaryReal_fiber_at_most_two hdC heC hfC
      ((not_ne_iff.mp hdne).trans (not_ne_iff.mp hene).symm)
      ((not_ne_iff.mp hdne).trans heq.symm) with h | h | h
    · exact hde h
    · exact hdf h
    · exact hef h
  exact ⟨binaryReal f, (mem_binaryImage_iff _ _).mpr ⟨f, hf, rfl⟩,
    binaryReal_interval_of_prefix hcC hfC hn ha hb hlo hup hsf, hfne⟩

def IsPerfectRealSet (P : V) : Prop :=
  (∃ S, S ⊆ realBasicCodes V ∧ P = realClosedFrom S) ∧ IsNonempty P ∧
    ∀ x ∈ P, ∀ a ∈ internalRationals V, ∀ b ∈ internalRationals V,
      x ∈ realInterval a b → ∃ y ∈ P, y ∈ realInterval a b ∧ y ≠ x

instance isPerfectRealSet_definable : ℒₛₑₜ-predicate[V] IsPerfectRealSet := by
  unfold IsPerfectRealSet
  definability

theorem binaryPerfectImage_perfect {T : V} (hT : IsPerfectTree T) :
    IsPerfectRealSet (binaryImage (treeBody T)) := by
  refine ⟨binaryTreeImage_closed hT.1, ?_, ?_⟩
  · obtain ⟨c, hc, _⟩ := perfectTree_branch_through hT hT.2.1
    exact ⟨binaryReal c, (mem_binaryImage_iff _ _).mpr ⟨c, hc, rfl⟩⟩
  · intro x hx a ha b hb hxi
    exact binaryPerfectImage_no_isolated hT hx ha hb hxi

end ZFVP
