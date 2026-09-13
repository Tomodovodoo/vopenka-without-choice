import ZFVP.ModelTheory.WoodinSparseGenericReflection
import ZFVP.ModelTheory.WoodinSparseRankAgreement
import ZFVP.ModelTheory.WoodinSparseEndpointZFC

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {Ω θ : V} [IsOrdinal Ω] [IsOrdinal θ]
variable (hΩ : IsWoodinSupercompact Ω) (hθ : IsWoodinSupercompact θ) (hAC : ¬InternalChoice V)
  {G : Set V} (hG : IsExternalForcingGeneric
    ((forcingCodeP (kpair.π₁ (woodinIterationRec Ω))) ‘ Ω)
    ((forcingCodeR (kpair.π₁ (woodinIterationRec Ω))) ‘ Ω) G) (hθΩ : θ ∈ Ω)
local notation "A" => woodinSparseFixedPointContext hΩ hAC hG hθΩ
local notation "E" => woodinSparseGenericContext hΩ hAC (subset_refl Ω) hG
local notation "J" => woodinSparseFixedPointContext_inclusion hΩ hAC hG hθΩ

noncomputable def woodinSparseRankMap :
    SetDomain (hierarchy ((A).check θ)) → SetDomain (hierarchy ((E).check Ω)) := fun x ↦
  ⟨J x.val, by
    have hx := ((J).mem_iff x.val (hierarchy ((A).check θ))).mpr x.property
    rw [woodinSparseFixedPointContext_inclusion_hierarchy] at hx
    exact hierarchy_mono (IsOrdinal.toIsTransitive.transitive _ (((E).check_mem_iff _ _).mpr hθΩ)) _ hx⟩

include hθ in
/-- Actual finite-formula comparison between a marked sparse rank and endpoint. -/
theorem woodinSparseRankMap_preservesFormula {k n : ℕ}
    (hfix : (kpair.π₂ (woodinIterationRec Ω)) ‘ θ = θ)
    (hΩC : Cn (k + 1) Ω) (hθC : Cn (k + 1) θ) (φ : SetTheorySemisentence n)
    (hφ : IsSigmaFormula (k + 1) (woodinSparseForcingTranslation φ))
    (hneg : IsSigmaFormula (k + 1) (woodinSparseForcingTranslation (∼φ)))
    (a : Fin n → SetDomain (hierarchy ((A).check θ))) :
    φ.Evalb a ↔ φ.Evalb (fun i ↦ woodinSparseRankMap hΩ hAC hG hθΩ (a i)) := by
  have hc := woodinSparseFixedPointContext_low_name_coverage hΩ hAC hG hθΩ hfix
  choose τ hτ he using fun i ↦ hc (a i).val (a i).property
  let v : Fin n → SetDomain (hierarchy θ) := fun i ↦ ⟨(τ i).val, hτ i⟩
  have hv : ∀ i, IsForcingName (A).P (v i).val := fun i ↦ (τ i).property
  let σ : Fin n → ForcingName (E).P := fun i ↦
    ⟨(τ i).val, ((τ i).property).mono (woodinSparse_prefix_carrier_subset hΩ hAC hθΩ)⟩
  have hσ : ∀ i, (σ i).val ∈ hierarchy Ω := fun i ↦
    hierarchy_mono (IsOrdinal.toIsTransitive.transitive _ hθΩ) _ (hτ i)
  have hs := woodinSparse_fixedPoint_standardFormula_truth hΩ hAC hG hθΩ hfix φ τ hτ
  have ht := woodinSparse_endpoint_standardFormula_truth hΩ hAC hG φ σ hσ
  have hmid := woodinSparse_genericMeets_reflection hΩ hθ hAC hG hθΩ hΩC hθC φ hφ hneg v hv
  have heA : (fun i ↦ (⟨(A).ofName (τ i), (A).ofName_mem_checked_hierarchy _ (hτ i)⟩ :
      SetDomain (hierarchy ((A).check θ)))) = a := by
    funext i
    exact Subtype.ext (he i).symm
  have heE : (fun i ↦ (⟨(E).ofName (σ i), (E).ofName_mem_checked_hierarchy _ (hσ i)⟩ :
      SetDomain (hierarchy ((E).check Ω)))) =
        (fun i ↦ woodinSparseRankMap hΩ hAC hG hθΩ (a i)) := by
    funext i
    apply Subtype.ext
    change (E).ofName (σ i) = J (a i).val
    rw [he i]
    rfl
  rw [heA] at hs
  rw [heE] at ht
  exact hs.trans (hmid.trans ht.symm)

end ZFVP

