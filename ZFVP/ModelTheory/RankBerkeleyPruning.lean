import ZFVP.ModelTheory.RankBerkeleyDescent
import ZFVP.ModelTheory.TransitiveModelGodel

/-! Consistency of adjoining the absence of nonzero rank-Berkeley cardinals to ZF+VP. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory Entailment

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem IsNonzeroRankBerkeley.models_Godel {δ : V} (hδ : IsNonzeroRankBerkeley δ) :
    V↓[ℒₛₑₜ] ⊧ setProgramGodelSentence := by
  obtain ⟨Λ, hΛ, _, _, _, hZF, hVP⟩ := hδ.exists_internalZF_codedVP
  let := hΛ
  let := hierarchy_transitive Λ
  let : Nonempty (SetDomain (hierarchy Λ)) := by
    obtain ⟨x, hx⟩ := hZF.1.1.nonempty
    exact ⟨⟨x, hx⟩⟩
  exact transitiveZFVP_model_impliesGodel ((satisfiesOpenCodes_zfVP_iff _).mpr ⟨hZF, hVP⟩)

theorem zf_proves_nonzeroRankBerkeley_Godel :
    𝗭𝗙 ⊢ nonzeroRankBerkeleyExistenceSentence 🡒 setProgramGodelSentence := by
  apply SetTheory.provable_of_models.{0}
  intro V _ _ _
  have h : nonzeroRankBerkeleyExistenceSentence.Evalb (![] : Fin 0 → V) →
      V↓[ℒₛₑₜ] ⊧ setProgramGodelSentence := by
    rw [eval_nonzeroRankBerkeleyExistenceSentence]
    rintro ⟨δ, hδ⟩
    exact hδ.models_Godel
  simpa [models_iff, Semiformula.Realize, Semiformula.Evalb] using h

theorem nonzeroRankBerkeley_unprovable [Consistent zfVPTheory] :
    zfVPTheory ⊬ nonzeroRankBerkeleyExistenceSentence := by
  let : 𝗭𝗙 ⪯ zfVPTheory := WeakerThan.ofSubset Set.subset_union_left
  intro h
  have himp : zfVPTheory ⊢ nonzeroRankBerkeleyExistenceSentence 🡒 setProgramGodelSentence :=
    WeakerThan.pbl zf_proves_nonzeroRankBerkeley_Godel
  exact setProgramGodelSentence_unprovable (himp ⨀ h)

theorem consistent_no_nonzeroRankBerkeley (h : Consistent zfVPTheory) :
    Consistent (insert (∼nonzeroRankBerkeleyExistenceSentence) zfVPTheory) := by
  let := h
  exact unprovable_iff_consistent_adjoin.mp nonzeroRankBerkeley_unprovable

end ZFVP
