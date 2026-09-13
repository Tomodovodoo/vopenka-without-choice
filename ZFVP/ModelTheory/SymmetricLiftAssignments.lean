import ZFVP.ModelTheory.SymmetricLiftBounded
import ZFVP.SetTheory.FunctionUnion

/-! The symmetric graph acts componentwise on internally finite assignments. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace SymmetricLiftData

variable {S : SymmetricContext V} {U W f : V}
variable [IsTransitive U] [IsTransitive W]
variable [Nonempty (SetDomain U)] [Nonempty (SetDomain W)]
variable [(SetDomain U)↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [(SetDomain W)↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable (L : SymmetricLiftData S U W f)

theorem graph_value_apply {g A x : S.Model} (hg : g ∈ domain L.graph)
    (hA : A ∈ domain L.graph) (hfunc : IsFunction g) (hdom : domain g = A) (hx : x ∈ A) :
    (L.graph ‘ g) ‘ (L.graph ‘ x) = L.graph ‘ (g ‘ x) := by
  let := hfunc
  have hm := L.graph_value_function_domain hg hA hfunc hdom
  let := hm.1
  have hd := hdom.symm ▸ hx
  have hpair : ⟨x, g ‘ x⟩ₖ ∈ g := kpair_value_mem hd
  have hxv := kpair_components_mem_transitive (L.graph_domain_transitive.mem_trans hpair hg)
  have hp := (L.graph_bounded_defined_iff boundedPairMemberFormula_bounded
    (fun v ↦ ⟨v 1, v 2⟩ₖ ∈ v 0) ![g, x, g ‘ x]
      (by simp [Fin.forall_fin_iff_zero_and_forall_succ, hg, hxv.1, hxv.2])).mp hpair
  exact value_eq_of_kpair_mem hp

theorem graph_value_assignment {n b : S.Model} (hn : n ∈ (ω : S.Model))
    (hb : b ∈ domain L.graph ^ n) : L.graph ‘ b = compose b L.graph := by
  have hbD := function_mem_sequenceSupport (subset_refl (domain L.graph)) hn hb
  have hfun : IsFunction b := IsFunction.of_mem hb
  have hm := L.graph_value_function_domain hbD (IsCodingSupport.natural_mem hn) hfun
    (domain_eq_of_mem_function hb)
  have hgraph : L.graph ∈ range L.graph ^ domain L.graph := IsFunction.mem_function L.graph
  have : IsFunction (L.graph ‘ b) := hm.1
  have : IsFunction (compose b L.graph) := IsFunction.of_mem (compose_function hb hgraph)
  apply functions_eq_of_domain_values
  · rw [hm.2, L.graph_value_natural hn, domain_eq_of_mem_function (compose_function hb hgraph)]
  · intro i hi
    have hin : i ∈ n := by simpa only [hm.2, L.graph_value_natural hn] using hi
    have hiω := IsOrdinal.toIsTransitive.mem_trans hin hn
    have he := L.graph_value_apply hbD (IsCodingSupport.natural_mem hn) hfun
      (domain_eq_of_mem_function hb) hin
    rw [L.graph_value_natural hiω] at he
    exact he.trans (value_compose_of_mem_function hb hgraph hin).symm

theorem graph_value_assignment_fixed {n b : S.Model} (hn : n ∈ (ω : S.Model))
    (hb : b ∈ domain L.graph ^ n) (hvalues : ∀ i ∈ n, L.graph ‘ (b ‘ i) = b ‘ i) :
    L.graph ‘ b = b := by
  rw [L.graph_value_assignment hn hb]
  have hgraph : L.graph ∈ range L.graph ^ domain L.graph := IsFunction.mem_function L.graph
  have : IsFunction b := IsFunction.of_mem hb
  have : IsFunction (compose b L.graph) := IsFunction.of_mem (compose_function hb hgraph)
  apply functions_eq_of_domain_values
  · rw [domain_eq_of_mem_function (compose_function hb hgraph), domain_eq_of_mem_function hb]
  · intro i hi
    have hin := domain_eq_of_mem_function (compose_function hb hgraph) ▸ hi
    rw [value_compose_of_mem_function hb hgraph hin, hvalues i hin]

end SymmetricLiftData
end ZFVP
