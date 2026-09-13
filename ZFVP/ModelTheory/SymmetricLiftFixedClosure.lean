import ZFVP.ModelTheory.SymmetricLift

/-! A fixed transitive closure of the coded symmetric system supplies the lift hypotheses. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def symmetricSystemCode (P R Γ F : V) : V := ⟨P, ⟨R, ⟨Γ, F⟩ₖ⟩ₖ⟩ₖ

instance symmetricSystemCode_definable : ℒₛₑₜ-function₄[V] symmetricSystemCode := by
  unfold symmetricSystemCode
  definability

theorem symmetricSystemCode_components_mem {P R Γ F T : V} [IsTransitive T]
    (h : symmetricSystemCode P R Γ F ∈ T) : P ∈ T ∧ R ∈ T ∧ Γ ∈ T ∧ F ∈ T := by
  obtain ⟨hP, hRF⟩ := kpair_components_mem_transitive h
  obtain ⟨hR, hGF⟩ := kpair_components_mem_transitive hRF
  obtain ⟨hΓ, hF⟩ := kpair_components_mem_transitive hGF
  exact ⟨hP, hR, hΓ, hF⟩

namespace SymmetricLiftData

variable {S : SymmetricContext V} {U W f : V} [IsTransitive U]

theorem of_fixedClosure (h : IsCodedMembershipEmbedding U W f)
    (hcode : symmetricSystemCode S.P S.R S.Γ S.F ∈ U)
    (hfix : ∀ z ∈ transitiveClosure ({symmetricSystemCode S.P S.R S.Γ S.F} : V), f ‘ z = z) :
    SymmetricLiftData S U W f := by
  have hU := symmetricSystemCode_components_mem hcode
  let T := transitiveClosure ({symmetricSystemCode S.P S.R S.Γ S.F} : V)
  have hT : IsTransitive T := transitiveClosure_transitive _
  have hTC : symmetricSystemCode S.P S.R S.Γ S.F ∈ T := subset_transitiveClosure _ _ (by simp)
  have hc := symmetricSystemCode_components_mem hTC
  exact ⟨h, hU.1, hU.2.1, hU.2.2.1, hU.2.2.2,
    hfix _ hc.1, hfix _ hc.2.1, hfix _ hc.2.2.1, hfix _ hc.2.2.2,
    fun p hp ↦ hfix p (hT.mem_trans hp hc.1),
    fun π hπ ↦ hfix π (hT.mem_trans hπ hc.2.2.1)⟩

end SymmetricLiftData

variable {S : SymmetricContext V} {U W f : V}
variable [IsTransitive U] [IsTransitive W]
variable [Nonempty (SetDomain U)] [Nonempty (SetDomain W)]
variable [(SetDomain U)↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [(SetDomain W)↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem exists_symmetric_lift_of_fixedClosure (h : IsCodedMembershipEmbedding U W f)
    (hcode : symmetricSystemCode S.P S.R S.Γ S.F ∈ U)
    (hfix : ∀ z ∈ transitiveClosure ({symmetricSystemCode S.P S.R S.Γ S.F} : V), f ‘ z = z) :
    ∃ E : S.Model, IsFunction E ∧
      (∀ x, x ∈ domain E ↔ ∃ σ : S.Name, σ.val ∈ U ∧ x = S.ofName σ) ∧
      ∀ σ : S.Name, σ.val ∈ U → ∃ τ : S.Name,
        τ.val = f ‘ σ.val ∧ E ‘ (S.ofName σ) = S.ofName τ := by
  let L := SymmetricLiftData.of_fixedClosure h hcode hfix
  refine ⟨L.graph, L.graph_isFunction, L.graph_domain, ?_⟩
  intro σ hσ
  exact ⟨L.imageName σ hσ, rfl, L.graph_value σ hσ⟩

end ZFVP

