import ZFVP.ModelTheory.SymmetricLiftSyntax
import ZFVP.Syntax.EndExtensionSatisfaction
import ZFVP.Syntax.UniformSemanticTransport

/-! Transfer structure codes and full internal satisfaction through the ordinary lift. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace SymmetricLiftData

variable {S : SymmetricContext V} {U W f : V}
variable [IsTransitive U] [IsTransitive W]
variable [Nonempty (SetDomain U)] [Nonempty (SetDomain W)]
variable [(SetDomain U)↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [(SetDomain W)↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable (L : SymmetricLiftData S U W f)

theorem graph_domain_source_inclusion (x : S.Model) (hx : x ∈ domain L.graph) :
    ∃ y : L.sourceContext.Model, L.sourceInclusion y = S.inclusion x := L.graph_domain_source x hx

theorem graph_agrees_inclusions (x : S.Model) (hx : x ∈ domain L.graph)
    (y : L.sourceContext.Model) (hy : L.sourceInclusion y = S.inclusion x) :
    S.inclusion (L.graph ‘ x) = L.targetInclusion (L.ordinaryLift y) := L.graph_agrees_ordinaryLift x hx y hy

theorem graph_languageCode_iff {language : S.Model} (hl : language ∈ domain L.graph) :
    IsLanguageCode (L.graph ‘ language) ↔ IsLanguageCode language := by
  obtain ⟨a, ha⟩ := L.graph_domain_source_inclusion language hl
  rw [← S.inclusion.languageCode_iff, L.graph_agrees_inclusions language hl a ha,
    L.targetInclusion.languageCode_iff, L.ordinaryLift.map_languageCode_iff,
    ← L.sourceInclusion.languageCode_iff, ha]
  exact S.inclusion.languageCode_iff language

theorem graph_structureCode_iff {language M : S.Model}
    (hl : language ∈ domain L.graph) (hm : M ∈ domain L.graph) :
    IsStructureCode (L.graph ‘ language) (L.graph ‘ M) ↔ IsStructureCode language M := by
  obtain ⟨a, ha⟩ := L.graph_domain_source_inclusion language hl
  obtain ⟨m, hm'⟩ := L.graph_domain_source_inclusion M hm
  rw [← S.inclusion.structureCode_iff,
    L.graph_agrees_inclusions language hl a ha, L.graph_agrees_inclusions M hm m hm',
    L.targetInclusion.structureCode_iff, L.ordinaryLift.map_structureCode_iff,
    ← L.sourceInclusion.structureCode_iff, ha, hm']
  exact S.inclusion.structureCode_iff language M

theorem graph_value_structureDomain {language M : S.Model} (hM : IsStructureCode language M)
    (hm : M ∈ domain L.graph) : L.graph ‘ (structureDomain M) = structureDomain (L.graph ‘ M) := by
  have hd : structureDomain M ∈ domain L.graph := by
    have hc := hM.2.1 ▸ hm
    exact (kpair_components_mem_transitive hc).1
  obtain ⟨m, hm'⟩ := L.graph_domain_source_inclusion M hm
  have hdm : L.sourceInclusion (structureDomain m) = S.inclusion (structureDomain M) := by
    rw [L.sourceInclusion.map_structureDomain, hm', ← S.inclusion.map_structureDomain]
  apply S.inclusion.injective
  rw [L.graph_agrees_inclusions _ hd _ hdm,
    L.ordinaryLift.map_definedFunction₁ structureDomainFormula structureDomain structureDomain,
    L.targetInclusion.map_structureDomain,
    ← L.graph_agrees_inclusions M hm m hm', S.inclusion.map_structureDomain]

theorem graph_satisfies_iff {language Γ M e n φ b : S.Model} (hL : IsLanguageCode language)
    (hl : language ∈ domain L.graph) (hΓ : Γ ∈ domain L.graph) (hm : M ∈ domain L.graph)
    (he : e ∈ domain L.graph) (hn : n ∈ domain L.graph) (hφ : φ ∈ domain L.graph)
    (hb : b ∈ domain L.graph) :
    Satisfies (L.graph ‘ language) (L.graph ‘ Γ) (L.graph ‘ M) (L.graph ‘ e)
      (L.graph ‘ n) (L.graph ‘ φ) (L.graph ‘ b) ↔ Satisfies language Γ M e n φ b := by
  obtain ⟨a, ha⟩ := L.graph_domain_source_inclusion language hl
  obtain ⟨g, hg⟩ := L.graph_domain_source_inclusion Γ hΓ
  obtain ⟨m, hm'⟩ := L.graph_domain_source_inclusion M hm
  obtain ⟨c, hc⟩ := L.graph_domain_source_inclusion e he
  obtain ⟨k, hk⟩ := L.graph_domain_source_inclusion n hn
  obtain ⟨ψ, hψ⟩ := L.graph_domain_source_inclusion φ hφ
  obtain ⟨d, hd⟩ := L.graph_domain_source_inclusion b hb
  have hLa : IsLanguageCode a := by
    rw [← L.sourceInclusion.languageCode_iff, ha]
    exact (S.inclusion.languageCode_iff language).mpr hL
  have hLe := (L.graph_languageCode_iff hl).mpr hL
  have hLj := (L.ordinaryLift.map_languageCode_iff a).mpr hLa
  rw [← S.inclusion.satisfies_iff hLe,
    L.graph_agrees_inclusions language hl a ha, L.graph_agrees_inclusions Γ hΓ g hg,
    L.graph_agrees_inclusions M hm m hm', L.graph_agrees_inclusions e he c hc,
    L.graph_agrees_inclusions n hn k hk, L.graph_agrees_inclusions φ hφ ψ hψ,
    L.graph_agrees_inclusions b hb d hd,
    L.targetInclusion.satisfies_iff hLj, L.ordinaryLift.map_satisfies_iff,
    ← L.sourceInclusion.satisfies_iff hLa, ha, hg, hm', hc, hk, hψ, hd]
  exact S.inclusion.satisfies_iff hL Γ M e n φ b

end SymmetricLiftData
end ZFVP
