import ZFVP.SetTheory.SupercompactUltrapowerBound
import ZFVP.SetTheory.SupercompactInaccessible
import ZFVP.SetTheory.MagidorUltrapowerReflection
import ZFVP.SetTheory.MagidorVopenkaForwardSharp

/-! Normal fine measures yield high-critical small embeddings into inaccessible ranks. -/

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem IsChoicelessInaccessible.isZFRank {γ : V} (hγ : IsChoicelessInaccessible γ) :
    IsZFRank γ := by
  let := hγ.1
  let := rankDomain_nonempty hγ.2.1
  exact ⟨inferInstance, hγ.rankCriterion.models_zf⟩

theorem IsSupercompact.highCritical_inaccessible_target (hAC : InternalChoice V)
    (hSC : ∀ α : V, IsOrdinal α → ∃ κ : V, α ∈ κ ∧ IsSupercompact κ)
    {κ γ η : V} (hκ : IsSupercompact κ) (hγ : IsChoicelessInaccessible γ)
    (hκγ : κ ∈ γ) (hη : η ∈ κ) :
    ∃ β ∈ κ, IsChoicelessInaccessible β ∧ ∃ α ∈ β, η ∈ α ∧ ∃ e : V,
      IsCodedMembershipEmbedding (hierarchy β) (hierarchy γ) e ∧
      IsCriticalPoint (hierarchy β) e α ∧ e ‘ α = κ := by
  let := hκ.isOrdinal
  let := hγ.1
  let lam := hartogsNumber (hierarchy γ)
  have hlam : IsInitialOrdinal lam := hartogsNumber_initial _
  let := hlam.1
  have hγlam : γ ∈ lam := ordinal_cardLE_iff_mem_hartogsNumber.mp
    (cardLE_of_subset (ordinal_subset_hierarchy γ))
  have hκlam : κ ∈ lam := IsOrdinal.toIsTransitive.mem_trans hκγ hγlam
  have hcard : hierarchy γ ≤# lam := (wellOrderable_iff_cardLE_hartogsNumber _).mp
    (wellOrderable_of_internalChoice hAC _)
  obtain ⟨θ, hlamθ, hθSC⟩ := hSC lam hlam.1
  have hθ := hθSC.inaccessible hAC
  let := hθ.1
  let := rankDomain_nonempty hθ.2.1
  let := hθ.rankCriterion.models_zf
  have hγθ := IsOrdinal.toIsTransitive.mem_trans hγlam hlamθ
  have hκθ := IsOrdinal.toIsTransitive.mem_trans hκlam hlamθ
  have h0lam : (∅ : V) ∈ lam := IsOrdinal.toIsTransitive.mem_trans
    (IsOrdinal.toIsTransitive.mem_trans (by simp) hκ.2.1) hκlam
  obtain ⟨M, j, hM, hMne, hj, hc, hjκ, _, hclosed, _⟩ :=
    supercompact_ultrapower_stage_above hAC hκ hlam
      (IsOrdinal.toIsTransitive.transitive _ hκlam) h0lam hθ.regular hlamθ hκθ
  let := hM
  let : Nonempty (SetDomain M) := by
    obtain ⟨x, hx⟩ := hMne.nonempty
    exact ⟨⟨x, hx⟩⟩
  have hMZF : (SetDomain M)↓[ℒₛₑₜ] ⊧* 𝗭𝗙 := by
    refine ⟨fun ψ hψ ↦ ?_⟩
    have hs : ψ.Evalb (![] : Fin 0 → SetDomain (hierarchy θ)) :=
      Theory.models (SetDomain (hierarchy θ)) 𝗭𝗙 hψ
    have ht := (hj.eval_semisentence ψ ![]).mp hs
    have hv : hj.toFunction ∘ (![] : Fin 0 → SetDomain (hierarchy θ)) =
        (![] : Fin 0 → SetDomain M) := by funext i; exact Fin.elim0 i
    rw [hv] at ht
    exact ht
  let := hMZF
  let := hierarchy_transitive θ
  let := hj.value_ordinal hκ.isOrdinal hc.mem_domain
  exact inaccessibleMagidor_of_closed_embedding hθ.rankCriterion.2.2.1 hj hc hγ hκγ hγθ
    (IsOrdinal.toIsTransitive.mem_trans hγlam hjκ) hη hclosed hcard

end ZFVP
