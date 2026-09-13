import ZFVP.ModelTheory.EmbeddingNaturalFixation
import ZFVP.SetTheory.BoundedFunctionDomain
import ZFVP.SetTheory.FunctionUnion
import ZFVP.Syntax.LiftSubstitution

/-! Images of internal function graphs and internally finite parameter assignments. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace IsCodedMembershipEmbedding

variable {A B f : V} [hA : IsTransitive A] [IsTransitive B]

theorem value_function_domain (h : IsCodedMembershipEmbedding A B f) {g X : V}
    (hg : g ∈ A) (hX : X ∈ A) (hfunc : IsFunction g) (hdom : domain g = X) :
    IsFunction (f ‘ g) ∧ domain (f ‘ g) = f ‘ X :=
  (h.bounded_defined_iff boundedFunctionDomainFormula_bounded
    (fun v ↦ IsFunction (v 0) ∧ domain (v 0) = v 1) ![g, X] (by simp [hg, hX])).mp ⟨hfunc, hdom⟩

theorem function_argument_mem {g x : V} [IsFunction g] (hg : g ∈ A) (hx : x ∈ domain g) :
    x ∈ A ∧ g ‘ x ∈ A :=
  kpair_components_mem_transitive (hA.mem_trans (kpair_value_mem hx) hg)

theorem value_apply (h : IsCodedMembershipEmbedding A B f) {g X x : V}
    (hg : g ∈ A) (hX : X ∈ A) (hfunc : IsFunction g) (hdom : domain g = X) (hx : x ∈ X) :
    (f ‘ g) ‘ (f ‘ x) = f ‘ (g ‘ x) := by
  let := hfunc
  have hm := h.value_function_domain hg hX hfunc hdom
  let := hm.1
  have hd := hdom.symm ▸ hx
  obtain ⟨hxA, hvA⟩ := function_argument_mem hg hd
  have hpair : ⟨x, g ‘ x⟩ₖ ∈ g := kpair_value_mem hd
  have hp := (h.bounded_defined_iff boundedPairMemberFormula_bounded
    (fun v ↦ ⟨v 1, v 2⟩ₖ ∈ v 0) ![g, x, g ‘ x]
      (by simp [Fin.forall_fin_iff_zero_and_forall_succ, hg, hxA, hvA])).mp hpair
  exact value_eq_of_kpair_mem hp

end IsCodedMembershipEmbedding

namespace IsCodedMembershipEmbedding

variable {A B f : V} [IsCodingSupport A] [IsTransitive B]

theorem value_assignment (h : IsCodedMembershipEmbedding A B f) {n b : V}
    (hn : n ∈ (ω : V)) (hbA : b ∈ A) (hb : b ∈ A ^ n) : f ‘ b = compose b f := by
  have hfun : IsFunction b := IsFunction.of_mem hb
  have hm := h.value_function_domain hbA (IsCodingSupport.natural_mem hn) hfun (domain_eq_of_mem_function hb)
  have : IsFunction (f ‘ b) := hm.1
  have : IsFunction (compose b f) := IsFunction.of_mem (compose_function hb h.function)
  apply functions_eq_of_domain_values
  · rw [hm.2, h.value_natural hn, domain_eq_of_mem_function (compose_function hb h.function)]
  · intro i hi
    have hin : i ∈ n := by simpa [hm.2, h.value_natural hn] using hi
    have hiω := IsOrdinal.toIsTransitive.mem_trans hin hn
    have he := h.value_apply hbA (IsCodingSupport.natural_mem hn) hfun (domain_eq_of_mem_function hb) hin
    rw [h.value_natural hiω] at he
    exact he.trans (value_compose_of_mem_function hb h.function hin).symm

theorem value_assignment_fixed (h : IsCodedMembershipEmbedding A B f) {n b : V}
    (hn : n ∈ (ω : V)) (hbA : b ∈ A) (hb : b ∈ A ^ n)
    (hvalues : ∀ i ∈ n, f ‘ (b ‘ i) = b ‘ i) : f ‘ b = b := by
  rw [h.value_assignment hn hbA hb]
  have : IsFunction b := IsFunction.of_mem hb
  have : IsFunction (compose b f) := IsFunction.of_mem (compose_function hb h.function)
  apply functions_eq_of_domain_values
  · rw [domain_eq_of_mem_function (compose_function hb h.function), domain_eq_of_mem_function hb]
  · intro i hi
    have hin := domain_eq_of_mem_function (compose_function hb h.function) ▸ hi
    rw [value_compose_of_mem_function hb h.function hin, hvalues i hin]

end IsCodedMembershipEmbedding

end ZFVP
