import ZFVP.ModelTheory.SchmerlInternalSubstitutionTransport
import ZFVP.ModelTheory.SchmerlInternalQInterchange

/-! The syntactic Q interchange schema transports its source fragment
and actual binder swap. No semantic or cardinal-preservation assumption
is needed for this direction. -/

namespace ZFVP.Infinitary.Internal.EndExtension
open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V W : Type*} [SetStructure V] [SetStructure W]
  [Nonempty V] [Nonempty W] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
  (j : MembershipEndExtension V W)

theorem map_qInterchangeCode (φ ψ : V) :
    j (qInterchangeCode φ ψ) = qInterchangeCode (j φ) (j ψ) := by
  simp only [qInterchangeCode, map_impCode, map_negCode, map_qCode, map_exsCode]

theorem qInterchangeAxiom_map {L n χ : V} (hχ : IsQInterchangeAxiom L n χ) :
    IsQInterchangeAxiom (j L) (j n) (j χ) := by
  obtain ⟨F, φ, ψ, hF, hφ, rfl, rfl⟩ := hχ
  have hs : succ n ∈ (ω : V) := IsTransitive.ω.mem_trans (by simp) (hF.node hφ).1
  have hn : n ∈ (ω : V) := IsTransitive.ω.mem_trans (by simp) hs
  refine ⟨j F, j φ, j (swapCode L F n φ), fragment_map j hF, ?_, map_swapCode j hF hn φ, ?_⟩
  · simpa only [j.map_kpair, j.map_succ] using (j.mem_iff _ _).mpr hφ
  · exact map_qInterchangeCode j _ _

end ZFVP.Infinitary.Internal.EndExtension
