import ZFVP.ModelTheory.SchmerlCodedSelectedTree

/-! Consequences of the genuine internally coded source, including its
ambient member-trace smallness and the constructed tree forcing data. -/

set_option autoImplicit false

namespace ZFVP.Schmerl

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def binaryIdentityRepresentation {D E : V} (hD : IsNonempty D) (hE : E ⊆ D ×ˢ D) :
    BinaryRelationRepresentation (V := V) (BinaryRelationDomain D E) where
  carrier := D
  relation := E
  carrier_nonempty := hD
  relation_subset := hE
  equiv := Equiv.refl _
  mem_iff _ _ := Iff.rfl

theorem IsCodedFinSmall.binary_trace_countable {D E : V} (hD : IsNonempty D)
    [Nonempty (BinaryRelationDomain D E)] [(BinaryRelationDomain D E)↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
    (h : IsCodedFinSmall (binaryRelationStructureCode D E))
    (a : BinaryRelationDomain D E) (ha : IsInternallyFinite a) :
    IsInternallyCountable ({x ∈ D ; ⟨x, a.val⟩ₖ ∈ E} : V) := by
  have hc := h a.val (by simpa only [binaryRelationStructureCode_domain] using a.property)
    ((codedUnary_finite_iff hD a).mpr ha)
  have he : codedMemberTrace (binaryRelationStructureCode D E) a.val = {x ∈ D ; ⟨x, a.val⟩ₖ ∈ E} := by
    apply mem_ext
    intro x
    rw [codedMemberTrace_binary_iff hD a.property, mem_sep_iff]
  exact he ▸ hc

theorem isCodedFinSmall_binary_iff {D E : V} (hD : IsNonempty D)
    [Nonempty (BinaryRelationDomain D E)] [(BinaryRelationDomain D E)↓[ℒₛₑₜ] ⊧* 𝗭𝗙] :
    IsCodedFinSmall (binaryRelationStructureCode D E) ↔
      ∀ a : BinaryRelationDomain D E, IsInternallyFinite a →
        IsInternallyCountable ({x ∈ D ; ⟨x, a.val⟩ₖ ∈ E} : V) := by
  constructor
  · exact fun h a ha ↦ h.binary_trace_countable hD a ha
  · intro h a ha hf
    have haD : a ∈ D := by simpa only [binaryRelationStructureCode_domain] using ha
    let b : BinaryRelationDomain D E := ⟨a, haD⟩
    have hb := (codedUnary_finite_iff hD b).mp hf
    have he : codedMemberTrace (binaryRelationStructureCode D E) a = {x ∈ D ; ⟨x, b.val⟩ₖ ∈ E} := by
      apply mem_ext
      intro x
      rw [codedMemberTrace_binary_iff hD haD, mem_sep_iff]
    exact he.symm ▸ h b hb

/-- All structural forcing premises are derived here. The separate internal
bound on full cofinal branches is not asserted by this theorem. -/
theorem IsCodedRubinFinSmallSource.selectedClassTree {M : V} (h : IsCodedRubinFinSmallSource M) :
    ∃ c, IsInternalCofinalStrictChain (hartogsNumber (ω : V)) (codedOrdinals M) (codedOrdinalOrder M) c ∧
      InternalRankedTree (codedSelectedClassNodes M (hartogsNumber (ω : V)) c)
        (codedSelectedClassOrder M (hartogsNumber (ω : V)) c) (hartogsNumber (ω : V))
        (codedSelectedClassRank M (hartogsNumber (ω : V)) c) ∧
      IsForcingPoset (codedSelectedClassNodes M (hartogsNumber (ω : V)) c)
        (codedSelectedClassOrder M (hartogsNumber (ω : V)) c) ∧
      (∀ x ∈ codedSelectedClassNodes M (hartogsNumber (ω : V)) c,
        ∀ y ∈ codedSelectedClassNodes M (hartogsNumber (ω : V)) c,
        ⟨x, y⟩ₖ ∈ codedSelectedClassOrder M (hartogsNumber (ω : V)) c →
        (codedSelectedClassRank M (hartogsNumber (ω : V)) c) ‘ x =
          (codedSelectedClassRank M (hartogsNumber (ω : V)) c) ‘ y → x = y) ∧
      codedSelectedClassNodes M (hartogsNumber (ω : V)) c ≤# hartogsNumber (ω : V) := by
  obtain ⟨⟨D, E, rfl, hE⟩, hZF, hcard, hRubin, _⟩ := h
  have hD : IsNonempty D := by simpa only [binaryRelationStructureCode_domain] using hZF.valid.domain_nonempty
  let R := binaryIdentityRepresentation hD hE
  let : Nonempty (BinaryRelationDomain D E) := binaryRelationDomain_nonempty hD
  let : (BinaryRelationDomain D E)↓[ℒₛₑₜ] ⊧* 𝗭𝗙 := R.models_zf_of_isCodedZFModel hZF
  obtain ⟨c, hc, ht, hP, hinj⟩ := R.exists_selectedClassTree_of_codedRubin hRubin
  refine ⟨c, hc, ht, hP, hinj, ?_⟩
  apply (cardLE_of_subset ?_).trans hcard
  intro x hx
  have hxT := ((mem_codedSelectedClassNodes _ _ _ _).mp hx).1
  exact ((mem_codedUnarySet _ _ _).mp hxT).1

end ZFVP.Schmerl
