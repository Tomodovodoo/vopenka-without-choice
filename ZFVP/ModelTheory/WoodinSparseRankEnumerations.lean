import ZFVP.ModelTheory.WoodinSparseStageInvariant
import ZFVP.ModelTheory.WoodinRankConstruction

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem woodinSparseStageCode_forces_rankEnumerations {Ω θ : V} [IsOrdinal θ]
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ∈ Ω) :
    ForcesRankEnumerations ((forcingCodeP (woodinSparseStageCode θ)) ‘ θ)
      ((forcingCodeR (woodinSparseStageCode θ)) ‘ θ) ∅ θ
      ((kpair.π₂ (woodinIterationRec θ)) ‘ θ) := by
  let := hΩ.inaccessible.1
  have hsub : θ ⊆ Ω := IsOrdinal.toIsTransitive.transitive _ hθ
  have hr := woodinIteration_rankStages hΩ θ hθ
  intro q hq
  obtain ⟨p, hp, rfl⟩ := woodinSparseRealizationMap_surjective hΩ hAC hsub q hq
  have hv (o : V) : (fun i : Fin 2 ↦ checkName o (![θ, (kpair.π₂ (woodinIterationRec θ)) ‘ θ] i)) =
      ![checkName o θ, checkName o ((kpair.π₂ (woodinIterationRec θ)) ‘ θ)] := by
    funext i
    exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun t ↦ Fin.elim0 t) j) i
  have ht := woodinSparseRealizationMap_checked_forcing_iff hΩ hAC hsub
    shortRankEnumerationsFormula ![θ, (kpair.π₂ (woodinIterationRec θ)) ‘ θ] hp
  rw [hv, hv] at ht
  exact ht.mp (hr p hp)

theorem ForcingContext.woodinSparse_rankEnumerations (A : ForcingContext V)
    {Ω θ : V} [IsOrdinal θ]
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ∈ Ω)
    (hP : A.P = (forcingCodeP (woodinSparseStageCode θ)) ‘ θ)
    (hR : A.R = (forcingCodeR (woodinSparseStageCode θ)) ‘ θ) (ho : A.one = ∅) :
    HasShortRankEnumerations (A.check θ) (A.check ((kpair.π₂ (woodinIterationRec θ)) ‘ θ)) := by
  apply A.rankEnumerations_of_forced
  rw [hP, hR, ho]
  exact woodinSparseStageCode_forces_rankEnumerations hΩ hAC hθ

theorem ForcingContext.woodinSparseSource_rankEnumerations (A : ForcingContext V)
    {Ω θ : V} [IsOrdinal θ]
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ∈ Ω)
    (hP : A.P = (forcingCodeP (woodinSparseSourceStageCode θ)) ‘ (woodinSourceIndex θ))
    (hR : A.R = (forcingCodeR (woodinSparseSourceStageCode θ)) ‘ (woodinSourceIndex θ)) (ho : A.one = ∅) :
    HasShortRankEnumerations (A.check θ) (A.check ((kpair.π₂ (woodinIterationRec θ)) ‘ θ)) := by
  rw [(woodinSparseSourceStageCode_row (mem_succ_self θ)).1] at hP
  rw [(woodinSparseSourceStageCode_row (mem_succ_self θ)).2] at hR
  exact A.woodinSparse_rankEnumerations hΩ hAC hθ hP hR ho

end ZFVP
