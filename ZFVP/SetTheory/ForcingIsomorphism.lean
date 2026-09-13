import ZFVP.SetTheory.FinitePartialFunctions
import ZFVP.SetTheory.InverseFunction

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def IsForcingIsomorphism (P R Q S f : V) : Prop :=
  f ∈ Q ^ P ∧ Injective f ∧ range f = Q ∧
    ∀ p ∈ P, ∀ q ∈ P, ⟨p, q⟩ₖ ∈ R ↔ ⟨f ‘ p, f ‘ q⟩ₖ ∈ S

instance isForcingIsomorphism_definable : ℒₛₑₜ-relation₅[V] IsForcingIsomorphism := by
  unfold IsForcingIsomorphism
  definability

theorem reverseInclusion_isomorphism_of_inverse {P Q : V}
    (F G : V → V) (hF : ℒₛₑₜ-function₁ F)
    (hFP : ∀ p ∈ P, F p ∈ Q) (hGQ : ∀ q ∈ Q, G q ∈ P)
    (hGF : ∀ p ∈ P, G (F p) = p) (hFG : ∀ q ∈ Q, F (G q) = q)
    (hFm : ∀ p ∈ P, ∀ q ∈ P, p ⊆ q → F p ⊆ F q)
    (hGm : ∀ p ∈ Q, ∀ q ∈ Q, p ⊆ q → G p ⊆ G q) :
    IsForcingIsomorphism P (reverseInclusionOrder P) Q (reverseInclusionOrder Q)
      (definableGraph P F hF) := by
  let f := definableGraph P F hF
  have hf : f ∈ Q ^ P := definableGraph_mem_function_of_mapsTo _ _ _ _ hFP
  let := IsFunction.of_mem hf
  refine ⟨hf, ?_, ?_, ?_⟩
  · intro p q z hp hq
    obtain ⟨hpP, hzp⟩ := (pair_mem_definableGraph_iff _ F hF p z).mp hp
    obtain ⟨hqP, hzq⟩ := (pair_mem_definableGraph_iff _ F hF q z).mp hq
    have he := congrArg G (hzp.symm.trans hzq)
    simpa only [hGF p hpP, hGF q hqP] using he
  · apply SetTheory.subset_antisymm (range_subset_of_mem_function hf)
    intro q hq
    have hv : f ‘ (G q) = q := (value_definableGraph _ _ _ (hGQ q hq)).trans (hFG q hq)
    exact hv ▸ value_mem_range hf (hGQ q hq)
  · intro p hp q hq
    rw [pair_mem_reverseInclusionOrder, pair_mem_reverseInclusionOrder,
      value_definableGraph _ _ _ hp, value_definableGraph _ _ _ hq]
    simp only [hp, hq, hFP p hp, hFP q hq, true_and]
    constructor
    · exact hFm q hq p hp
    · intro h
      have hh := hGm (F q) (hFP q hq) (F p) (hFP p hp) h
      simpa only [hGF q hq, hGF p hp] using hh

end ZFVP
