import ZFVP.SetTheory.NameAction
import ZFVP.SetTheory.BoundedCodingPrimitives

/-! Functional tables for the recursive action on a subname-closed family. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def IsNameActionTable (P π C T f : V) : Prop :=
  f ∈ T ^ C ∧ ∀ u ∈ C, ∀ z, z ∈ f ‘ u ↔
    ∃ s ∈ C, ∃ p ∈ P, ⟨s, p⟩ₖ ∈ u ∧ z = ⟨f ‘ s, π ‘ p⟩ₖ

theorem IsNameActionTable.correct {P π C T f : V} (h : IsNameActionTable P π C T f)
    (hC : IsSubnameClosed C) (hnames : ∀ u ∈ C, IsForcingName P u) :
    ∀ u ∈ C, f ‘ u = nameAction π u := by
  apply projectedRank_induction C (fun x : V ↦ x) (by definability)
    (fun u ↦ f ‘ u = nameAction π u) (by definability)
  intro u hu ih
  apply mem_ext
  intro z
  rw [h.2 u hu z, mem_nameAction_iff (hnames u hu)]
  constructor
  · rintro ⟨s, hs, p, _, hsp, rfl⟩
    exact ⟨s, p, hsp, by rw [ih s hs (rank_subname_lt hsp)]⟩
  · rintro ⟨s, p, hsp, rfl⟩
    have hs := hC u hu s (mem_domain_of_kpair_mem hsp)
    exact ⟨s, hs, p, forcingName_condition (hnames u hu) hsp, hsp,
      by rw [ih s hs (rank_subname_lt hsp)]⟩

theorem nameActionTable_exists (P π C : V) (hC : IsSubnameClosed C)
    (hnames : ∀ u ∈ C, IsForcingName P u) : ∃ T f, IsNameActionTable P π C T f := by
  let hf : ℒₛₑₜ-function₁[V] (nameAction π) := by definability
  refine ⟨repl (nameAction π) hf C, definableGraph C (nameAction π) hf,
    definableGraph_mem_function C (nameAction π) hf, ?_⟩
  intro u hu z
  rw [value_definableGraph _ _ _ hu, mem_nameAction_iff (hnames u hu)]
  constructor
  · rintro ⟨s, p, hsp, rfl⟩
    have hs := hC u hu s (mem_domain_of_kpair_mem hsp)
    exact ⟨s, hs, p, forcingName_condition (hnames u hu) hsp, hsp,
      by rw [value_definableGraph _ _ _ hs]⟩
  · rintro ⟨s, hs, p, _, hsp, rfl⟩
    exact ⟨s, p, hsp, by rw [value_definableGraph _ _ _ hs]⟩

end ZFVP
