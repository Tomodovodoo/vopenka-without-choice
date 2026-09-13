import ZFVP.ModelTheory.RankEmbeddingDictionary

/-! Recover the components of a pair in the range of a rank embedding. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def sigmaOnePairShapeFormula : SetTheorySemisentence 1 :=
  “p. ∃ x y, !boundedKpairFormula p x y”

theorem sigmaOnePairShapeFormula_sigmaOne : IsSigmaFormula 1 sigmaOnePairShapeFormula :=
  .exs (.exs (.bounded (boundedKpairFormula_bounded.subst _)))

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance sigmaOnePairShapeFormula_defined :
    ℒₛₑₜ-predicate[V] (fun p ↦ ∃ x y : V, p = ⟨x, y⟩ₖ) via sigmaOnePairShapeFormula :=
  ⟨fun v ↦ by simp [sigmaOnePairShapeFormula]⟩

theorem rankEmbedding_pair_preimages {k : ℕ} {δ ε f p x y : V}
    (hδ : Cn (k + 1) δ) (hε : Cn (k + 1) ε)
    (h : IsCodedMembershipEmbedding (hierarchy δ) (hierarchy ε) f)
    (hp : p ∈ hierarchy δ) (he : f ‘ p = ⟨x, y⟩ₖ) :
    ∃ u v, u ∈ hierarchy δ ∧ v ∈ hierarchy δ ∧ p = ⟨u, v⟩ₖ ∧ f ‘ u = x ∧ f ‘ v = y := by
  let := hδ.ordinal
  let := hε.ordinal
  let := hierarchy_transitive δ
  let := hierarchy_transitive ε
  have hs := rankEmbedding_defined_iff hδ hε h
    (sigmaOnePairShapeFormula_sigmaOne.mono (by omega))
    (fun v ↦ ∃ x y : V, v 0 = ⟨x, y⟩ₖ) ![p] (by simpa using hp)
  have hshape : ∃ u v : V, p = ⟨u, v⟩ₖ := hs.mpr ⟨x, y, he⟩
  obtain ⟨u, v, hpeq⟩ := hshape
  have hp' : ⟨u, v⟩ₖ ∈ hierarchy δ := by rwa [← hpeq]
  obtain ⟨hu, hv⟩ := kpair_components_mem_transitive hp'
  have he' : f ‘ ⟨u, v⟩ₖ = ⟨x, y⟩ₖ := by rwa [← hpeq]
  have hcomp := kpair_inj ((h.value_pair hu hv hp').symm.trans he')
  exact ⟨u, v, hu, hv, hpeq, hcomp.1, hcomp.2⟩

end ZFVP
