import ZFVP.ModelTheory.ProductGenericConverseEquiv
import ZFVP.ModelTheory.QuotientEquivalence
import ZFVP.ModelTheory.LevyProductEquivalence
import ZFVP.ModelTheory.CohenGenericReals
import ZFVP.SetTheory.BaireCore
import ZFVP.SetTheory.EndExtensionLevyCollapse

/-! Compatibility of the model equivalences with names and values of the intermediate models:
the two-step equivalence on lifted names, the quotient equivalence on values of the subalgebra
realization, the Levy product equivalence on values of the sub-collapse realization; the union of
the finite initial segments of a real; the checked tree order. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace ForcingContext

theorem modelCast_ofName {A B : ForcingContext V} (h : A = B) (τ : ForcingName A.P) :
    modelCast h (A.ofName τ) = B.ofName ⟨τ.val, h ▸ τ.property⟩ := by
  subst h
  rfl

theorem modelCast_ofName' {A B : ForcingContext V} (h : A = B) (τ : ForcingName A.P) (σ : ForcingName B.P)
    (hσ : σ.val = τ.val) : modelCast h (A.ofName τ) = B.ofName σ := by
  rw [modelCast_ofName]
  congr 1
  exact Subtype.ext hσ.symm

/-- The quotient equivalence on values of the subalgebra realization. -/
theorem quotientEquiv_value (A : ForcingContext V) {D : V} (hD : IsCompleteSubalgebra A.P A.R D)
    (y : (A.subalgebraContext hD).Model) :
    A.quotientEquiv hD ((A.subalgebraRealization hD).value y) = (A.quotientContext hD).check y := by
  obtain ⟨τ, rfl⟩ := (A.subalgebraContext hD).ofName_surjective y
  have h := A.booleanContext.restrictRealization_value_ofName
    (A.subalgebraConditions_subset_boolean (D := D)) (A.top_mem_subalgebraConditions hD)
    (hD.trace_generic A.order A.generic) τ
  have h' : (A.subalgebraRealization hD).value ((A.subalgebraContext hD).ofName τ) =
      A.booleanContext.ofName (A.subalgebraNameLift hD τ) := h
  rw [h']
  exact A.quotientEquiv_lift hD τ

end ForcingContext

section

variable {κ : V} (β : V) [IsOrdinal β] (hβ : β ⊆ κ) {G : Set V}
  (hG : IsExternalForcingGeneric (levyCollapse κ) (levyOrder κ) G)

/-- The Levy product equivalence on values of the sub-collapse realization. -/
theorem levyProductEquiv_value (y : (levySubContext β hβ hG).Model) :
    levyProductEquiv β hβ hG ((levySubRealization β hβ hG).value y) =
      (levyProductContext β hβ hG).check y := by
  obtain ⟨τ, rfl⟩ := (levySubContext β hβ hG).ofName_surjective y
  rw [levySubRealization_value_ofName]
  exact levyProductEquiv_lift β hβ hG τ

end

section

variable (C : ForcingContext V) {P₂ R₂ one₂ : V} (h₂ : IsForcingPreorder P₂ R₂)
  (t₂ : IsForcingTop P₂ R₂ one₂) (Q : ForcingContext C.Model)
  (hP : Q.P = C.check P₂) (hR : Q.R = C.check R₂) (hone : Q.one = C.check one₂)

/-- The two-step equivalence on names lifted from the first factor. -/
theorem twoStepEquiv_lift (τ : ForcingName C.P) :
    twoStepEquiv C h₂ t₂ Q hP hR hone
      ((productContext C.order C.top h₂ t₂ (combinedGeneric_generic C Q hP hR)).ofName
        (productNameLift C.order C.top h₂ t₂ (combinedGeneric_generic C Q hP hR) τ)) =
      Q.check (C.ofName τ) := by
  unfold twoStepEquiv
  simp only [Equiv.trans_apply]
  have h := productEquiv_lift C.order C.top h₂ t₂ (combinedGeneric_generic C Q hP hR) τ
  rw [h, ForcingContext.modelCast_check]
  apply (ForcingContext.castContextEquiv (firstFactorContext_combined C h₂ Q hP hR).symm Q).injective
  have hm : ForcingContext.modelCast (firstFactorContext_combined C h₂ Q hP hR).symm (C.ofName τ) =
      (firstFactorContext C.order C.top h₂ (combinedGeneric_generic C Q hP hR)).ofName τ :=
    ForcingContext.modelCast_ofName' (A := C)
      (B := firstFactorContext C.order C.top h₂ (combinedGeneric_generic C Q hP hR))
      (firstFactorContext_combined C h₂ Q hP hR).symm τ τ rfl
  rw [Equiv.apply_symm_apply, ForcingContext.castContextEquiv_check, hm]

end

/-- A real is the union of its finite initial segments. -/
theorem sUnion_initialSegments {x : V} (hx : x ∈ cantorSpace V) :
    ⋃ˢ {s ∈ binarySequences V ; s ⊆ x} = x := by
  apply mem_ext
  intro z
  rw [mem_sUnion_iff]
  constructor
  · rintro ⟨s, hs, hzs⟩
    exact (mem_sep_iff.mp hs).2 z hzs
  · intro hz
    obtain ⟨n, hn, i, _, rfl⟩ := mem_prod_iff.mp (subset_prod_of_mem_function hx _ hz)
    refine ⟨x ↾ (succ n), mem_sep_iff.mpr ⟨restrict_mem_binarySequences hx (ω_succ_closed hn),
      restrict_subset x (succ n)⟩, ?_⟩
    exact kpair_mem_restrict_iff.mpr ⟨hz, mem_succ_iff.mpr (Or.inl rfl)⟩

theorem isDenseSequences_of_forcingDense {D : V}
    (hD : ForcingDense (binarySequences V) (sequenceOrder ((2 : ℕ) : V)) D) : IsDenseSequences D := by
  refine ⟨hD.1, fun s hs ↦ ?_⟩
  obtain ⟨t, ht, hts⟩ := hD.2 s hs
  exact ⟨t, ht, ((pair_mem_sequenceOrder_iff _ _ _).mp hts).2.2⟩

theorem forcingDense_of_isDenseSequences {D : V} (hD : IsDenseSequences D) :
    ForcingDense (binarySequences V) (sequenceOrder ((2 : ℕ) : V)) D := by
  refine ⟨hD.1, fun s hs ↦ ?_⟩
  obtain ⟨t, ht, hst⟩ := hD.2 s hs
  exact ⟨t, ht, (pair_mem_sequenceOrder_iff _ _ _).mpr ⟨hD.1 t ht, hs, hst⟩⟩

theorem subset_of_meets {D x : V} (hD : D ⊆ binarySequences V) (hx : x ∈ cantorSpace V)
    (h : Meets D x) : ∃ s ∈ D, s ⊆ x := by
  obtain ⟨s, hs, hxs⟩ := h
  exact ⟨s, hs, (subset_iff_restrict_eq hx (hD s hs)).mpr hxs⟩

namespace ForcingContext

variable (A : ForcingContext V)

theorem check_sequenceOrder :
    A.check (sequenceOrder ((2 : ℕ) : V)) = sequenceOrder ((2 : ℕ) : A.Model) := by
  unfold sequenceOrder
  have h1 := A.checkEmbedding.map_reverseInclusionOrder (finiteSequences ((2 : ℕ) : V))
  have h2 := A.checkEmbedding.map_finiteSequences ((2 : ℕ) : V)
  have h3 := A.checkEmbedding.map_numeral 2
  rw [h2, h3] at h1
  exact h1

end ForcingContext

end ZFVP
