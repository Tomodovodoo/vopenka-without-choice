import ZFVP.ModelTheory.UsubaBoundCoordinates
import ZFVP.ModelTheory.UsubaLocalUnionQuotientBound

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
local notation "T" => usubaForcingTower (V := V)

theorem usubaQuotientBoundAt_successor_normalized [Countable V] {θ i k p α : V}
    [IsOrdinal θ] [IsOrdinal i] [IsOrdinal k] [IsOrdinal α]
    (hik : i ⊆ k) (hkθ : succ k ⊆ θ) (hp : p ∈ (T).P i)
    (f : ForcingName ((T).P i)) (hf : ForcesUsubaQuotientSequence θ i p f.val α)
    (hDC : ∀ (G : Set V) (hG : IsExternalForcingGeneric ((T).P i) ((T).R i) G), p ∈ G →
      InternalDependentChoiceAt ((usubaStageContext i hG).check α))
    (hclosure : ∀ (G : Set V) (hG : IsExternalForcingGeneric ((T).P i) ((T).R i) G), p ∈ G →
      let A := usubaStageContext i hG
      IsForcingClosedThrough (A.projectionQuotient ((T).P k) ((T).projection i k))
        (forcingSeparativeOrder (A.projectionQuotient ((T).P k) ((T).projection i k))
          (A.projectionQuotientOrder ((T).P k) ((T).R k) ((T).projection i k))) (A.check α))
    (hprev : ∀ l ∈ succ k, IsUsubaQuotientBoundAt θ i p f.val α l) :
    IsUsubaNormalizedQuotientBoundAt θ i p f.val α (succ k) := by
  let P := (T).P k
  let R := (T).R k
  let o := (T).top k
  let τ := (T).projection i k
  let E := (T).sectionMap i k
  let π := (T).projection i (succ k)
  let Q := usubaSaturatedPosetName P R
  let S := reverseInclusionOrderName P R Q
  let q := usubaQuotientBoundRec θ i p f.val k
  let μ : ForcingName ((T).P i) :=
    ⟨usubaBoundCoordinateName θ i f.val (succ k), usubaBoundCoordinateName_isName _ _ _ _⟩
  let ν := usubaLocalUnionName P R o (E ‘ p) (nameAction E μ.val)
  have hR := (T).order k inferInstance
  have ho := (T).top_spec k inferInstance
  have hbaseR := (T).order i inferInstance
  have hbaseo := (T).top_spec i inferInstance
  have hi : i ∈ succ k := mem_succ_iff.mpr (IsOrdinal.subset_iff.mp hik)
  have hisucc : i ⊆ succ k := IsOrdinal.toIsTransitive.transitive _ hi
  have hiθ : i ⊆ θ := subset_trans hisucc hkθ
  have hsplit := (T).splitProjection hik
  have hπ : π ∈ (T).P i ^ twoStepConditions P R Q ∅ := by
    rw [← usubaTower_P_succ]
    exact (T).projection_function i (succ k) inferInstance inferInstance hisucc
  have hcomp : ∀ c ∈ twoStepConditions P R Q ∅, τ ‘ (kpair.π₁ c) = π ‘ c := by
    intro c hc
    exact (usubaTower_projection_succ hik ((usubaTower_P_succ k).symm ▸ hc)).symm
  have hq : q ∈ P := (hprev k (mem_succ_self k)).1
  have hqb : τ ‘ q = p := by
    rw [usubaQuotientBoundRec_projects_of_membership hi (fun l hl ↦ (hprev l hl).1)
      k (mem_succ_self k) i hi, usubaQuotientBoundRec_base]
  have hqp : ⟨q, E ‘ p⟩ₖ ∈ R := (hsplit.below q hq p hp).mpr (hqb.symm ▸ hbaseR.2.1 p hp)
  have hdata (G : Set V) (hG : IsExternalForcingGeneric ((T).P i) ((T).R i) G) (hpG : p ∈ G) :
      let A := usubaStageContext i hG
      IsForcingDescending (A.projectionQuotient (twoStepConditions P R Q ∅) π)
        (forcingSeparativeOrder (A.projectionQuotient (twoStepConditions P R Q ∅) π)
          (A.projectionQuotientOrder (twoStepConditions P R Q ∅) (twoStepOrder P R Q S ∅) π))
        (A.check α) (A.ofName μ) ∧
      (∀ a ∈ A.check α,
        ⟨A.check q, (compose (A.ofName μ) (A.check (twoStepProjection P R Q ∅))) ‘ a⟩ₖ ∈
          forcingSeparativeOrder (A.projectionQuotient P τ) (A.projectionQuotientOrder P R τ)) ∧
      InternalDependentChoiceAt (A.check α) ∧
      IsForcingClosedThrough (A.projectionQuotient P τ)
        (forcingSeparativeOrder (A.projectionQuotient P τ) (A.projectionQuotientOrder P R τ)) (A.check α) := by
    let A := usubaStageContext i hG
    have hd := usubaQuotientSequence_semantics hiθ f hf hG hpG
    have hn := usubaBoundCoordinate_descending hisucc hkθ hG f hd
    rw [usubaTower_P_succ k, usubaTower_R_succ k] at hn
    have hb := ((usubaQuotientBoundAt_iff_generics hik hp f).mp (hprev k (mem_succ_self k))).2 G hG hpG
    have hfun := mem_function_of_mem_function_of_subset hd.1 sep_subset
    have he := usubaBoundCoordinate_successor_first hkθ hG f hfun
    refine ⟨hn, ?_, hDC G hG hpG, hclosure G hG hpG⟩
    intro a ha
    exact (congrArg (fun z : A.Model ↦ ⟨A.check q, z ‘ a⟩ₖ ∈
      forcingSeparativeOrder (A.projectionQuotient P τ) (A.projectionQuotientOrder P R τ)) he).mpr (hb.2 a ha)
  have hpair : ⟨q, ν⟩ₖ ∈ twoStepConditions P R Q ∅ :=
    transported_usuba_local_union_pair_mem hbaseR hbaseo hR ho hsplit hp hq hqp μ hπ hcomp hdata
  have hnorm : q ∈ atomicEquality P R ν (usubaSelectedUnionName P R o (nameAction E μ.val)) :=
    transported_usuba_local_union_normalization hbaseR hbaseo hR ho hsplit hp hq hqp μ hπ hcomp hdata
  have hqnext : usubaQuotientBoundRec θ i p f.val (succ k) = ⟨q, ν⟩ₖ := by
    rw [usubaQuotientBoundRec_successor hi]
    rfl
  refine ⟨?_, ?_⟩
  · apply (usubaQuotientBoundAt_iff_generics hisucc hp f).mpr
    refine ⟨?_, ?_⟩
    · rw [hqnext, usubaTower_P_succ k]
      exact hpair
    · intro G hG hpG
      let A := usubaStageContext i hG
      obtain ⟨hdesc, hbound, hdc, hclosed⟩ := hdata G hG hpG
      have hπpair : π ‘ ⟨q, ν⟩ₖ = p := by
        rw [← hcomp _ hpair, kpair.π₁_kpair, hqb]
      have hpQ : A.check ⟨q, ν⟩ₖ ∈ A.projectionQuotient (twoStepConditions P R Q ∅) π :=
        (A.check_mem_projectionQuotient_iff hπ).mpr ⟨hpair, hπpair.symm ▸ hpG⟩
      dsimp only
      rw [hqnext, usubaTower_P_succ k, usubaTower_R_succ k]
      exact ⟨hpQ, A.usuba_local_union_quotient_separative_bound hsplit hR ho hπ hcomp μ hdesc hbound
        (function_value_mem hsplit.maps hp) hqp hdc hclosed hpQ⟩
  · intro _ _
    simp only [sUnion_succ_of_transitive]
    exact hnorm

end ZFVP
