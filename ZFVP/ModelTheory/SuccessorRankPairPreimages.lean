import ZFVP.ModelTheory.SuccessorRankEmbedding
import ZFVP.ModelTheory.RankEmbeddingPairPreimages

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem successorRankEmbedding_sigma_iff {δ ε f : V} (hδ : Cn 1 δ) (hε : Cn 1 ε)
    (h : IsCodedMembershipEmbedding (hierarchy (succ δ)) (hierarchy (succ ε)) f)
    {n : ℕ} {φ : SetTheorySemisentence n} (hφ : IsSigmaFormula 1 φ)
    (v : Fin n → V) (hv : ∀ i, v i ∈ hierarchy δ) :
    φ.Evalb v ↔ φ.Evalb (fun i ↦ f ‘ (v i)) := by
  have he := successorRankEmbedding_pi_iff hδ hε h hφ.neg v hv
  have hn : ¬φ.Evalb v ↔ ¬φ.Evalb (fun i ↦ f ‘ (v i)) := by simpa using he
  simpa using not_congr hn

theorem successorRankEmbedding_pair_preimages {δ ε f p x y : V}
    (hδ : Cn 1 δ) (hε : Cn 1 ε)
    (h : IsCodedMembershipEmbedding (hierarchy (succ δ)) (hierarchy (succ ε)) f)
    (hp : p ∈ hierarchy δ) (he : f ‘ p = ⟨x, y⟩ₖ) :
    ∃ u v, u ∈ hierarchy δ ∧ v ∈ hierarchy δ ∧ p = ⟨u, v⟩ₖ ∧ f ‘ u = x ∧ f ‘ v = y := by
  let := hδ.ordinal
  let := hε.ordinal
  let := hierarchy_transitive δ
  let := hierarchy_transitive (succ δ)
  let := hierarchy_transitive (succ ε)
  have hs := successorRankEmbedding_sigma_iff hδ hε h sigmaOnePairShapeFormula_sigmaOne
    ![p] (by simpa using hp)
  have hshape : ∃ u v : V, p = ⟨u, v⟩ₖ := by
    have ht : sigmaOnePairShapeFormula.Evalb (fun i ↦ f ‘ (![p] i)) := by
      simpa using (show ∃ a b : V, f ‘ p = ⟨a, b⟩ₖ from ⟨x, y, he⟩)
    simpa using hs.mpr ht
  obtain ⟨u, v, hpeq⟩ := hshape
  have hp' : ⟨u, v⟩ₖ ∈ hierarchy δ := hpeq ▸ hp
  obtain ⟨hu, hv⟩ := kpair_components_mem_transitive hp'
  have hinc : hierarchy δ ⊆ hierarchy (succ δ) := hierarchy_mono
    (by intro z hz; exact mem_succ_iff.mpr (Or.inr hz))
  have hev : f ‘ ⟨u, v⟩ₖ = ⟨x, y⟩ₖ := by rwa [← hpeq]
  have hcomp := kpair_inj ((h.value_pair (hinc u hu) (hinc v hv) (hinc _ hp')).symm.trans hev)
  exact ⟨u, v, hu, hv, hpeq, hcomp.1, hcomp.2⟩

end ZFVP
