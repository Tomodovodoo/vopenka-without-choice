import ZFVP.ModelTheory.WoodinCanonicalBoundClosure
import ZFVP.ModelTheory.WoodinCanonicalBoundLift
import ZFVP.ModelTheory.WoodinCanonicalBoundInduction
import ZFVP.ModelTheory.WoodinBoundInvariantSemantics
import ZFVP.ModelTheory.QuotientLiftCompatibility
import ZFVP.ModelTheory.IterationQuotientClosure

/-! Final assembly of the canonical quotient bound at the new inverse-limit coordinate.
From the raw order comparison at `θ` we read off the forced separative bound for every
named descending sequence, and package it as the closure statement
`IterationQuotientClosedBelow (forcingInverseCode θ (woodinIterationPrefix θ)) i θ κ`. -/

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- The cardinal table of the prefix agrees at `i` with the cardinal table produced by the
recursion at `i`. -/
theorem woodinIterationCardinalPrefix_value_of_stages {δ θ i : V} [IsOrdinal θ]
    (hs : ∀ k ∈ θ, IsWoodinIteration δ (succ k) (kpair.π₁ (woodinIterationRec k))
      (kpair.π₂ (woodinIterationRec k))) (hi : i ∈ θ) :
    (woodinIterationCardinalPrefix θ) ‘ i = (kpair.π₂ (woodinIterationRec i)) ‘ i := by
  have h := woodinIterationHistory_of_stages hs
  unfold woodinIterationCardinalPrefix
  rw [h.cardinal_union_value hi (mem_succ_self i), woodinIterationHistory_cardinal_value hi]

/-- Closure of the raw inverse-limit projection quotient at the new coordinate `θ`.

The bound name is the check of the canonical bound history
`woodinQuotientBoundHistory θ i p f θ`; `hraw` is the raw order comparison that puts the
lift of a condition below the members of the sequence. The completed bound induction
supplies the history without an inverse-stage hypothesis. -/
theorem woodinInverse_raw_quotient_closedBelow [Countable V] {δ θ i : V} [IsOrdinal θ]
    (hs : ∀ k ∈ θ, IsWoodinIteration δ (succ k) (kpair.π₁ (woodinIterationRec k))
      (kpair.π₂ (woodinIterationRec k)))
    (hc : ∀ k ∈ θ, HasWoodinQuotientClosure (succ k) (kpair.π₁ (woodinIterationRec k))
      (kpair.π₂ (woodinIterationRec k)))
    (h0 : ∅ ∈ θ) (hi : i ∈ θ)
    (hraw : ∀ p ∈ (forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i,
      ∀ f : ForcingName ((forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i),
      ∀ α ∈ (kpair.π₂ (woodinIterationRec i)) ‘ i,
      ForcesWoodinQuotientSequence θ i p f.val α →
      ∀ d ∈ forcingInverseCodePoset θ (woodinIterationPrefix θ),
      ∀ e ∈ (forcingCodeP (woodinIterationPrefix θ)) ‘ i,
        ⟨e, d ‘ i⟩ₖ ∈ (forcingCodeR (woodinIterationPrefix θ)) ‘ i →
        ∀ r ∈ forcingInverseCodePoset θ (woodinIterationPrefix θ),
          ⟨r, woodinQuotientBoundHistory θ i p f.val θ⟩ₖ
            ∈ forcingInverseCodeOrder θ (woodinIterationPrefix θ) →
          ∀ b ∈ (forcingCodeP (woodinIterationPrefix θ)) ‘ i,
            ⟨b, (forcingThreadCoordinate (forcingInverseCodePoset θ (woodinIterationPrefix θ)) i) ‘ r⟩ₖ
              ∈ (forcingCodeR (woodinIterationPrefix θ)) ‘ i →
            ⟨b, e⟩ₖ ∈ (forcingCodeR (woodinIterationPrefix θ)) ‘ i →
            ⟨(woodinInverseCodeLift θ (woodinIterationPrefix θ) i) ‘ ⟨r, b⟩ₖ, d⟩ₖ
              ∈ forcingInverseCodeOrder θ (woodinIterationPrefix θ)) :
    IterationQuotientClosedBelow (forcingInverseCode θ (woodinIterationPrefix θ)) i θ
      ((woodinIterationCardinalPrefix θ) ‘ i) := by
  let := IsOrdinal.of_mem hi
  have hprefix := woodinIterationPrefix_of_stages hs
  have hcθ := hprefix.code
  let := (hprefix.inaccessible i hi).1
  have hηval : (woodinIterationCardinalPrefix θ) ‘ i = (kpair.π₂ (woodinIterationRec i)) ‘ i :=
    woodinIterationCardinalPrefix_value_of_stages hs hi
  have hPi : (forcingCodeP (woodinIterationPrefix θ)) ‘ i =
      (forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i :=
    woodinIterationPrefix_poset_value hs hi (mem_succ_self i)
  have hRi : (forcingCodeR (woodinIterationPrefix θ)) ‘ i =
      (forcingCodeR (kpair.π₁ (woodinIterationRec i))) ‘ i :=
    woodinIterationPrefix_order_value hs hi (mem_succ_self i)
  have hti : (forcingCodet (woodinIterationPrefix θ)) ‘ i =
      (forcingCodet (kpair.π₁ (woodinIterationRec i))) ‘ i :=
    woodinIterationPrefix_top_value hs hi (mem_succ_self i)
  have hcol := hcθ.system.inverseColumn h0 hcθ.subset_universe
  have hUpre : IsForcingPreorder (forcingInverseCodePoset θ (woodinIterationPrefix θ))
      (forcingInverseCodeOrder θ (woodinIterationPrefix θ)) := hcol.order.preorder
  have hRpre : IsForcingPreorder ((forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i)
      ((forcingCodeR (kpair.π₁ (woodinIterationRec i))) ‘ i) := by
    rw [← hPi, ← hRi]; exact hcθ.system.order.preorder i hi
  have htop : IsForcingTop ((forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i)
      ((forcingCodeR (kpair.π₁ (woodinIterationRec i))) ‘ i)
      ((forcingCodet (kpair.π₁ (woodinIterationRec i))) ‘ i) := by
    rw [← hPi, ← hRi, ← hti]; exact hcθ.system.tops.top i hi
  have hproj : IsForcingProjection ((forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i)
      ((forcingCodeR (kpair.π₁ (woodinIterationRec i))) ‘ i)
      (forcingInverseCodePoset θ (woodinIterationPrefix θ))
      (forcingInverseCodeOrder θ (woodinIterationPrefix θ))
      (forcingThreadCoordinate (forcingInverseCodePoset θ (woodinIterationPrefix θ)) i) := by
    rw [← hPi, ← hRi]; exact (woodinInverseCoordinate_split hs hi).projection
  have hL := woodinInverseCodeLift_spec hcθ h0 hi
  rw [hPi, hRi] at hL hraw
  have key : ForcesProjectionQuotientClosedBelow
      ((forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i)
      ((forcingCodeR (kpair.π₁ (woodinIterationRec i))) ‘ i)
      ((forcingCodet (kpair.π₁ (woodinIterationRec i))) ‘ i)
      (forcingInverseCodePoset θ (woodinIterationPrefix θ))
      (forcingInverseCodeOrder θ (woodinIterationPrefix θ))
      (forcingThreadCoordinate (forcingInverseCodePoset θ (woodinIterationPrefix θ)) i)
      ((woodinIterationCardinalPrefix θ) ‘ i) := by
    apply forcesProjectionQuotientClosedBelow_of_named_bounds hRpre htop hproj hUpre
    intro α hα p hp f hdesc
    have hαrec : α ∈ (kpair.π₂ (woodinIterationRec i)) ‘ i := hηval ▸ hα
    let := IsOrdinal.of_mem hα
    have hf : ForcesWoodinQuotientSequence θ i p f.val α := hdesc
    refine ⟨⟨checkName ((forcingCodet (kpair.π₁ (woodinIterationRec i))) ‘ i)
      (woodinQuotientBoundHistory θ i p f.val θ), checkName_isName htop.1 _⟩, ?_⟩
    apply projectionQuotient_bound_forced_of_generics hRpre htop hproj hUpre hp f
    intro G hG hpG
    let A : ForcingContext V := ⟨_, _, _, G, hRpre, htop, hG⟩
    have hmaps : (forcingThreadCoordinate (forcingInverseCodePoset θ (woodinIterationPrefix θ)) i)
        ∈ A.P ^ (forcingInverseCodePoset θ (woodinIterationPrefix θ)) := hproj.maps
    have hhist := woodinQuotientBoundHistory_mem_and_projects hs hc hi hαrec hp f hf
    have hqQ : A.check (woodinQuotientBoundHistory θ i p f.val θ) ∈
        A.projectionQuotient (forcingInverseCodePoset θ (woodinIterationPrefix θ))
          (forcingThreadCoordinate (forcingInverseCodePoset θ (woodinIterationPrefix θ)) i) := by
      refine (A.check_mem_projectionQuotient_iff hmaps).mpr ⟨hhist.1, ?_⟩
      show _ ∈ G
      rw [hhist.2]
      exact hpG
    refine ⟨hqQ, ?_⟩
    intro a ha
    have hdescG : IsForcingDescending
        (A.projectionQuotient (forcingInverseCodePoset θ (woodinIterationPrefix θ))
          (forcingThreadCoordinate (forcingInverseCodePoset θ (woodinIterationPrefix θ)) i))
        (forcingSeparativeOrder
          (A.projectionQuotient (forcingInverseCodePoset θ (woodinIterationPrefix θ))
            (forcingThreadCoordinate (forcingInverseCodePoset θ (woodinIterationPrefix θ)) i))
          (A.projectionQuotientOrder (forcingInverseCodePoset θ (woodinIterationPrefix θ))
            (forcingInverseCodeOrder θ (woodinIterationPrefix θ))
            (forcingThreadCoordinate (forcingInverseCodePoset θ (woodinIterationPrefix θ)) i)))
        (A.check α) (A.ofName f) :=
      woodinQuotientSequence_semantics hs hi f hf G hG hpG
    obtain ⟨w, hw, hwG, hval⟩ :=
      (A.mem_projectionQuotient_iff hmaps _).mp (function_value_mem hdescG.1 ha)
    have hwi : w ‘ i ∈ (forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i := by
      rw [← hPi]
      exact ((mem_forcingInverseLimit_iff _ _ _ _ _).mp hw).2.1 i hi
    have hwiG : w ‘ i ∈ A.G := by
      show _ ∈ G
      rwa [forcingThreadCoordinate_value hw] at hwG
    have hwQ : A.check w ∈
        A.projectionQuotient (forcingInverseCodePoset θ (woodinIterationPrefix θ))
          (forcingThreadCoordinate (forcingInverseCodePoset θ (woodinIterationPrefix θ)) i) :=
      (A.check_mem_projectionQuotient_iff hmaps).mpr ⟨hw, hwG⟩
    rw [hval]
    refine A.projectionQuotient_separative_of_lift
      (L := woodinInverseCodeLift θ (woodinIterationPrefix θ) i) hmaps hL hqQ hwQ hwiG ?_
    intro r hr hrq b hb hbr hbw
    exact hraw p hp f α hαrec hf w hw (w ‘ i) hwi (hRpre.2.1 _ hwi) r hr hrq b hb hbr hbw
  simpa only [IterationQuotientClosedBelow, forcingInverseCode, forcingThreadCode,
    forcingIterationCodeNext, forcingCodeP_code, forcingCodeR_code, forcingCodet_code,
    forcingCodeπ_code, forcingFamilyNext_old hi, forcingFamilyNext_new,
    forcingMatrixNext_column hi, forcingLimitProjectionColumn_value hi, hPi, hRi, hti,
    forcingInverseCodePoset, forcingInverseCodeOrder] using key

end ZFVP
