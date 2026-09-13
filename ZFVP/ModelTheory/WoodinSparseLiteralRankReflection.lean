import ZFVP.ModelTheory.WoodinSparseRankFormulaReflection
import ZFVP.SetTheory.TransitiveRestriction

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

include hΩ hAC hG hθΩ
noncomputable def woodinSparseLowerRankEquiv :
    SetDomain (hierarchy ((A).check θ)) ≃ SetDomain (hierarchy ((E).check θ)) := by
  let f : SetDomain (hierarchy ((A).check θ)) → SetDomain (hierarchy ((E).check θ)) := fun x ↦
    ⟨J x.val, by
      have hx := ((J).mem_iff x.val (hierarchy ((A).check θ))).mpr x.property
      rwa [woodinSparseFixedPointContext_inclusion_hierarchy] at hx⟩
  apply Equiv.ofBijective f
  constructor
  · intro x y h
    exact Subtype.ext ((J).injective (congrArg Subtype.val h))
  · intro y
    have hy : y.val ∈ J (hierarchy ((A).check θ)) :=
      Eq.mpr (congrArg (fun z : (E).Model ↦ y.val ∈ z)
        (woodinSparseFixedPointContext_inclusion_hierarchy hΩ hAC hG hθΩ)) y.property
    obtain ⟨x, hx, he⟩ := (J).endExtension _ y.val hy
    exact ⟨⟨x, hx⟩, Subtype.ext he.symm⟩

theorem woodinSparseLowerRankEquiv_mem
    (x y : SetDomain (hierarchy ((A).check θ))) :
    woodinSparseLowerRankEquiv hΩ hAC hG hθΩ x ∈ woodinSparseLowerRankEquiv hΩ hAC hG hθΩ y ↔ x ∈ y :=
  (J).mem_iff x.val y.val

include hθ in
theorem woodinSparseLowerRank_nonempty : Nonempty (SetDomain (hierarchy ((E).check θ))) := by
  have hA : Nonempty (SetDomain (hierarchy ((A).check θ))) :=
    WoodinSparseEndpointModel.rankModel_nonempty hθ hAC (woodinFixedPoint_stage_generic hΩ hAC hG hθΩ)
  exact ⟨woodinSparseLowerRankEquiv hΩ hAC hG hθΩ (Classical.choice hA)⟩

include hθ in
theorem woodinSparseLowerRank_models_zf :
    letI := woodinSparseLowerRank_nonempty hΩ hθ hAC hG hθΩ;
    (SetDomain (hierarchy ((E).check θ)))↓[ℒₛₑₜ] ⊧* 𝗭𝗙 := by
  letI : Nonempty (SetDomain (hierarchy ((A).check θ))) :=
    WoodinSparseEndpointModel.rankModel_nonempty hθ hAC (woodinFixedPoint_stage_generic hΩ hAC hG hθΩ)
  letI : Nonempty (SetDomain (hierarchy ((E).check θ))) := woodinSparseLowerRank_nonempty hΩ hθ hAC hG hθΩ
  have hA : (SetDomain (hierarchy ((A).check θ)))↓[ℒₛₑₜ] ⊧* 𝗭𝗙 :=
    WoodinSparseEndpointModel.rankModel_models_zf hθ hAC (woodinFixedPoint_stage_generic hΩ hAC hG hθΩ)
  let e := ElementaryMap.ofMembershipIso (woodinSparseLowerRankEquiv hΩ hAC hG hθΩ)
    (woodinSparseLowerRankEquiv_mem hΩ hAC hG hθΩ)
  exact ⟨fun φ hφ ↦ (e.models_sentence_iff φ).mp (hA.models_set hφ)⟩

include hθ in
/-- The literal inclusion of ranks in the endpoint preserves every fixed
formula in the derived forcing window. -/
theorem woodinSparseLowerRank_formula_reflection {k n : ℕ}
    (hfix : (kpair.π₂ (woodinIterationRec Ω)) ‘ θ = θ)
    (hΩC : Cn (k + 1) Ω) (hθC : Cn (k + 1) θ) (φ : SetTheorySemisentence n)
    (hφ : IsSigmaFormula (k + 1) (woodinSparseForcingTranslation φ))
    (hneg : IsSigmaFormula (k + 1) (woodinSparseForcingTranslation (∼φ)))
    (a : Fin n → SetDomain (hierarchy ((E).check θ))) :
    φ.Evalb a ↔ φ.Evalb (show Fin n → SetDomain (hierarchy ((E).check Ω)) from fun i ↦
      (⟨(a i).val, hierarchy_mono
        (IsOrdinal.toIsTransitive.transitive _ (((E).check_mem_iff _ _).mpr hθΩ)) _ (a i).property⟩ :
          SetDomain (hierarchy ((E).check Ω)))) := by
  let e := woodinSparseLowerRankEquiv hΩ hAC hG hθΩ
  let b := e.symm ∘ a
  have hs := eval_membershipIso e (woodinSparseLowerRankEquiv_mem hΩ hAC hG hθΩ) φ b Empty.elim
  have hz : e ∘ (Empty.elim : Empty → SetDomain (hierarchy ((A).check θ))) = Empty.elim := by
    funext x
    exact Empty.elim x
  have hb : e ∘ b = a := by funext i; exact e.apply_symm_apply (a i)
  rw [hz, hb] at hs
  have ht := woodinSparseRankMap_preservesFormula hΩ hθ hAC hG hθΩ hfix hΩC hθC φ hφ hneg b
  apply hs.symm.trans
  apply ht.trans
  apply Iff.of_eq
  apply congrArg (fun z : Fin n → SetDomain (hierarchy ((E).check Ω)) ↦ φ.Evalb z)
  funext i
  apply Subtype.ext
  exact congrArg (fun x : SetDomain (hierarchy ((E).check θ)) ↦ x.val) (e.apply_symm_apply (a i))

end ZFVP





