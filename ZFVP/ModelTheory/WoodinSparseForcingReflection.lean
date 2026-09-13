import ZFVP.ModelTheory.WoodinSparseForcingTranslation
import ZFVP.SetTheory.CnAbsoluteness

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- Ground finite reflection yields actual sparse forcing agreement on the
smaller rank, for any fixed formula whose concrete translation is in the window. -/
theorem woodinSparseForcing_rank_compare {Ω θ : V}
    (hΩ : IsWoodinSupercompact Ω) (hθ : IsWoodinSupercompact θ) (hAC : ¬InternalChoice V)
    (hθΩ : θ ∈ Ω) {k n : ℕ} (hΩC : Cn (k + 1) Ω) (hθC : Cn (k + 1) θ)
    (φ : SetTheorySemisentence n) (hφ : IsSigmaFormula (k + 1) (woodinSparseForcingTranslation φ))
    (v : Fin n → SetDomain (hierarchy θ))
    (hv : ∀ i, IsForcingName ((forcingCodeP (woodinSparseStageCode θ)) ‘ θ) (v i).val)
    (p : SetDomain (hierarchy θ)) :
    p.val ∈ classForcingFormula
      ((forcingCodeP (woodinSparseStageCode θ)) ‘ θ)
      ((forcingCodeR (woodinSparseStageCode θ)) ‘ θ)
      (fun x ↦ x ∈ hierarchy θ ∧ IsForcingName ((forcingCodeP (woodinSparseStageCode θ)) ‘ θ) x)
      (by definability) φ (standardTuple (fun i ↦ (v i).val)) ↔
    p.val ∈ classForcingFormula
      ((forcingCodeP (woodinSparseStageCode Ω)) ‘ Ω)
      ((forcingCodeR (woodinSparseStageCode Ω)) ‘ Ω)
      (fun x ↦ x ∈ hierarchy Ω ∧ IsForcingName ((forcingCodeP (woodinSparseStageCode Ω)) ‘ Ω) x)
      (by definability) φ (standardTuple (fun i ↦ (v i).val)) := by
  let := hΩ.inaccessible.1
  let := hθ.inaccessible.1
  let := rankDomain_nonempty hΩ.inaccessible.2.1
  let := rankDomain_nonempty hθ.inaccessible.2.1
  let := hΩ.inaccessible.rankCriterion.models_zf
  let := hθ.inaccessible.rankCriterion.models_zf
  have hsub : hierarchy θ ⊆ hierarchy Ω :=
    hierarchy_mono (IsOrdinal.toIsTransitive.transitive _ hθΩ)
  let lift : SetDomain (hierarchy θ) → SetDomain (hierarchy Ω) := fun x ↦ ⟨x.val, hsub x.val x.property⟩
  have hv' : ∀ i, IsForcingName ((forcingCodeP (woodinSparseStageCode Ω)) ‘ Ω) (lift (v i)).val :=
    fun i ↦ (hv i).mono (woodinSparse_prefix_carrier_subset hΩ hAC hθΩ)
  have ha := woodinSparseForcingTranslation_rank hθ hAC φ v hv p
  have hb := woodinSparseForcingTranslation_rank hΩ hAC φ (fun i ↦ lift (v i)) hv' (lift p)
  have hc := hθC.sigma_correct hφ (p :> v)
  have hd := hΩC.sigma_correct hφ ((lift p) :> (fun i ↦ lift (v i)))
  have hm : (fun i ↦ (((lift p) :> (fun j ↦ lift (v j))) i).val) =
      (fun i ↦ ((p :> v) i).val) := by
    funext i
    exact Fin.cases rfl (fun _ ↦ rfl) i
  rw [hm] at hd
  exact ha.symm.trans (hc.trans (hd.symm.trans hb))

end ZFVP
