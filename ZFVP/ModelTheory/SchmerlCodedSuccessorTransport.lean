import ZFVP.ModelTheory.SchmerlCodedExtensionRelabeling
import ZFVP.ModelTheory.SchmerlCodedCofinalSuccessor
import ZFVP.ModelTheory.InternalNamedSeparationOmission
import ZFVP.SetTheory.SchroederBernstein

/-! Successor properties survive a surjective coded elementary relabeling.
The parameter transport covers every internally finite raw formula. -/

set_option autoImplicit false

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem IsCodedElementaryEmbedding.inverse_of_range_eq {L M N h : V}
    (he : IsCodedElementaryEmbedding L M N h) (hrange : range h = structureDomain N) :
    IsCodedElementaryEmbedding L N M (converseGraph h) := by
  have hinv : converseGraph h ∈ structureDomain M ^ structureDomain N := by
    simpa only [hrange] using converseGraph_mem_function he.function he.injective
  have hid : compose (converseGraph h) h = SetTheory.identity (structureDomain N) := by
    have hc := compose_function hinv he.function
    let := IsFunction.of_mem hc
    apply functions_eq_of_domain_values (by
      rw [domain_eq_of_mem_function hc, domain_eq_of_mem_function (identity_mem_function _)])
    intro y hy
    rw [domain_eq_of_mem_function hc] at hy
    rw [value_compose_of_mem_function hinv he.function hy,
      value_converseGraph_value he.function he.injective (hrange.symm ▸ hy), identity_value hy]
  refine ⟨he.target, he.source, hinv, ?_⟩
  intro n hn φ hφ b hb
  have hs := he.satisfies_iff hn hφ (compose_function hb hinv)
  rw [graph_compose_assoc, hid, graph_compose_identity hb] at hs
  exact hs.symm

namespace Schmerl

theorem transportDefinition_comp (d e h : V) :
    transportDefinition (transportDefinition d e) h = transportDefinition d (compose e h) := by
  simp only [transportDefinition, definitionParameterCount_pair, definitionFormula_pair,
    definitionTuple_pair, graph_compose_assoc]

theorem elementary_codedMember_iff {M N h x y : V}
    (he : IsCodedElementaryEmbedding membershipLanguageCode M N h)
    (hx : x ∈ structureDomain M) (hy : y ∈ structureDomain M) :
    codedMember M x y ↔ codedMember N (h ‘ x) (h ‘ y) := by
  let := IsFunction.of_mem he.function
  have hs := he.satisfies_iff (by simp : (2 : V) ∈ (ω : V))
    (encodeMembershipFormula_mem (V := V) (“x y. x ∈ y” : SetTheorySemisentence 2))
    (standardTuple_mem_function ![x, y] (by simp [hx, hy]))
  rw [compose_standardTuple _ h (by simp [domain_eq_of_mem_function he.function, hx, hy])] at hs
  have ht : (fun i : Fin 2 ↦ h ‘ (![x, y] i)) = ![h ‘ x, h ‘ y] := by
    funext i
    fin_cases i <;> rfl
  rw [ht] at hs
  exact hs

theorem IsCodedInseparable.transport {M N h U W : V}
    (hUW : IsCodedInseparable M U W)
    (he : IsCodedElementaryEmbedding membershipLanguageCode M N h)
    (hrange : range h = structureDomain N) :
    IsCodedInseparable N (graphImage h U) (graphImage h W) := by
  let := IsFunction.of_mem he.function
  have hi := he.inverse_of_range_eq hrange
  refine ⟨graphImage_subset he.function, graphImage_subset he.function, ?_⟩
  rintro ⟨A, hA, hU, hW⟩
  obtain ⟨d, hd, hdA⟩ := hA.exists_unaryDefinition
  let B := unaryDefinitionSet M (transportDefinition d (converseGraph h))
  have hdM := transportDefinition_unary hd hi.function
  have hB : ∀ x ∈ structureDomain M, x ∈ B ↔ h ‘ x ∈ A := by
    intro x hx
    have hs := elementary_unaryDefinition_iff hi hd (function_value_mem he.function hx)
    rw [hdA, converseGraph_value_value he.function he.injective hx] at hs
    exact hs.symm
  have himage : ∀ X, ∀ x ∈ X, x ∈ structureDomain M → h ‘ x ∈ graphImage h X := by
    intro X x hx hxM
    exact (mem_graphImage_iff h X (h ‘ x)).mpr ⟨x, hx,
      kpair_value_mem (by simpa only [domain_eq_of_mem_function he.function] using hxM)⟩
  apply hUW.2.2
  refine ⟨B, unaryDefinitionSet_isCodedDefinable hdM, ?_, ?_⟩
  · intro x hx
    exact (hB x (hUW.1 x hx)).mpr (hU _ (himage U x hx (hUW.1 x hx)))
  · intro x hx hxB
    exact hW _ (himage W x hx (hUW.2.1 x hx)) ((hB x (hUW.2.1 x hx)).mp hxB)

theorem IsCodedFiniteTraceEmbedding.transport {L M N e h : V}
    (htrace : IsCodedFiniteTraceEmbedding L M e)
    (hef : e ∈ structureDomain M ^ structureDomain L)
    (he : IsCodedElementaryEmbedding membershipLanguageCode M N h)
    (hrange : range h = structureDomain N) :
    IsCodedFiniteTraceEmbedding L N (compose e h) := by
  let := IsFunction.of_mem he.function
  intro a ha hfin y hy hmem
  obtain ⟨z, hzy⟩ := mem_range_iff.mp (hrange.symm ▸ hy)
  have hz := (mem_of_mem_functions he.function hzy).1
  have hv := value_eq_of_kpair_mem hzy
  rw [← hv, value_compose_of_mem_function hef he.function ha] at hmem
  have hzm := (elementary_codedMember_iff he hz (function_value_mem hef ha)).mpr hmem
  obtain ⟨x, hxz⟩ := mem_range_iff.mp (htrace a ha hfin z hz hzm)
  exact mem_range_iff.mpr ⟨x, kpair_mem_compose_iff.mpr ⟨z, hxz, hzy⟩⟩

theorem IsCodedCofinalBounds.transport {L M N e c h : V}
    (hbound : IsCodedCofinalBounds L M e c)
    (hef : e ∈ structureDomain M ^ structureDomain L)
    (he : IsCodedElementaryEmbedding membershipLanguageCode M N h) :
    IsCodedCofinalBounds L N (compose e h) (compose c h) := by
  refine ⟨compose_function hbound.1 he.function, ?_⟩
  intro i hi
  have hci := function_value_mem hbound.1 hi
  have hdu := transportDefinition_unary (codedDirectedPosetIndex_spec hi).1 hef
  have hdb := transportDefinition_binary (codedDirectedPosetIndex_spec hi).2.1 hef
  rw [value_compose_of_mem_function hbound.1 he.function hi]
  refine ⟨?_, ?_⟩
  · simpa only [transportDefinition_comp] using
      (elementary_unaryDefinition_iff he hdu hci).mp (hbound.2 i hi).1
  · intro x hx
    have hxL := mem_power_iff.mp (function_value_mem (codedDirectedPosetDomains_mem L) hi) x hx
    have hxe := function_value_mem hef hxL
    rw [value_compose_of_mem_function hef he.function hxL]
    refine ⟨?_, fun heq ↦ (hbound.2 i hi).2 x hx |>.2 (he.value_injective hxe hci heq)⟩
    simpa only [transportDefinition_comp] using
      (elementary_binaryDefinition_iff he hdb hxe hci).mp ((hbound.2 i hi).2 x hx).1

end Schmerl
end ZFVP
