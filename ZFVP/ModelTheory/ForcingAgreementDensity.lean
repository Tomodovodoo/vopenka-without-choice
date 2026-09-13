import ZFVP.ModelTheory.ForcingSplitProjection
import ZFVP.ModelTheory.GenericRegularForcing

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- Every condition of the big poset is below the section of its own projection. -/
theorem IsForcingSplitProjection.section_below {P0 R0 P1 R1 π E q : V}
    (hsplit : IsForcingSplitProjection P0 R0 P1 R1 π E) (hR0 : IsForcingPreorder P0 R0)
    (hq : q ∈ P1) (hπq : π ‘ q ∈ P0) : ⟨q, E ‘ (π ‘ q)⟩ₖ ∈ R1 :=
  (hsplit.below q hq (π ‘ q) hπq).mpr (hR0.2.1 _ hπq)

/-- If the big generic filter meets `A1`, then the projected filter meets `A0`.
The set of small conditions below `π ‘ p` that lie in `A0` is dense below `π ‘ p`,
because a small condition with no such extension would sit in the negation of `A0`,
hence its section would sit in the negation of `A1`, which the lift of `p` refutes. -/
theorem agreement_forces_of_generic {P0 R0 P1 R1 π E A0 A1 : V} {G : Set V}
    (hR0 : IsForcingPreorder P0 R0)
    (hsplit : IsForcingSplitProjection P0 R0 P1 R1 π E)
    (hG : IsExternalForcingGeneric P1 R1 G)
    (hA1 : IsForcingDownwardClosed P1 R1 A1)
    (hagreeNeg : ∀ q ∈ P0,
      q ∈ forcingNegation P0 R0 A0 ↔ E ‘ q ∈ forcingNegation P1 R1 A1) :
    GenericMeets G A1 → GenericMeets (forcingProjectionGeneric P0 R0 π G) A0 := by
  rintro ⟨p, hpG, hpA1⟩
  have hpP1 : p ∈ P1 := hG.1.1 p hpG
  have hπp : π ‘ p ∈ P0 := function_value_mem hsplit.projection.maps hpP1
  have hdense : ForcingDenseBelow P0 R0 {q ∈ P0 ; ⟨q, π ‘ p⟩ₖ ∈ R0 ∧ q ∈ A0} (π ‘ p) := by
    refine ⟨fun q hq ↦ (mem_sep_iff.mp hq).1, ?_⟩
    intro q0 hq0 hq0p
    by_contra hno
    push_neg at hno
    have hneg : q0 ∈ forcingNegation P0 R0 A0 := by
      refine (mem_forcingNegation_iff _ _ _ _).mpr ⟨hq0, ?_⟩
      intro r hr hrq0 hrA0
      exact hno r (mem_sep_iff.mpr
        ⟨hr, hR0.2.2 r hr q0 hq0 (π ‘ p) hπp hrq0 hq0p, hrA0⟩) hrq0
    have hnegE : E ‘ q0 ∈ forcingNegation P1 R1 A1 := (hagreeNeg q0 hq0).mp hneg
    obtain ⟨r, hr, hrp, hrq⟩ := hsplit.projection.lift p hpP1 q0 hq0 hq0p
    have hrE : ⟨r, E ‘ q0⟩ₖ ∈ R1 := by
      refine (hsplit.below r hr q0 hq0).mpr ?_
      rw [hrq]
      exact hR0.2.1 q0 hq0
    exact ((mem_forcingNegation_iff _ _ _ _).mp hnegE).2 r hr hrE (hA1 p hpA1 r hr hrp)
  have hproj := hsplit.projection.generic hR0 hG
  have hmem := hsplit.projection.image_mem hR0 hG.1 hpG
  obtain ⟨q, hqG, hqD⟩ := externalForcingGeneric_meets_denseBelow hR0 hproj hmem hdense
  exact ⟨q, hqG, (mem_sep_iff.mp hqD).2.2⟩

/-- If the projected filter meets `A0`, then the big filter meets `A1`.
Only the filter property is used. -/
theorem agreement_generic_of_forces {P0 R0 P1 R1 π E A0 A1 : V} {G : Set V}
    (hsplit : IsForcingSplitProjection P0 R0 P1 R1 π E)
    (hG : IsExternalForcingFilter P1 R1 G)
    (hA1 : IsForcingDownwardClosed P1 R1 A1)
    (hagree : ∀ q ∈ P0, q ∈ A0 ↔ E ‘ q ∈ A1) :
    GenericMeets (forcingProjectionGeneric P0 R0 π G) A0 → GenericMeets G A1 := by
  rintro ⟨q, ⟨hqP0, q', hq'G, hq'q⟩, hqA0⟩
  have hq'P1 : q' ∈ P1 := hG.1 q' hq'G
  have hbelow : ⟨q', E ‘ q⟩ₖ ∈ R1 := (hsplit.below q' hq'P1 q hqP0).mpr hq'q
  exact ⟨q', hq'G, hA1 _ ((hagree q hqP0).mp hqA0) q' hq'P1 hbelow⟩

/-- Two forcing sets that agree along the section, together with their negations,
are met by the projected filter and by the big generic filter at the same time. -/
theorem genericMeets_agreement_iff {P0 R0 P1 R1 π E A0 A1 : V} {G : Set V}
    (hR0 : IsForcingPreorder P0 R0) (hR1 : IsForcingPreorder P1 R1)
    (hsplit : IsForcingSplitProjection P0 R0 P1 R1 π E)
    (hG : IsExternalForcingGeneric P1 R1 G)
    (hA0 : A0 ⊆ P0)
    (hA1 : IsForcingDownwardClosed P1 R1 A1)
    (hagree : ∀ q ∈ P0, q ∈ A0 ↔ E ‘ q ∈ A1)
    (hagreeNeg : ∀ q ∈ P0,
      q ∈ forcingNegation P0 R0 A0 ↔ E ‘ q ∈ forcingNegation P1 R1 A1) :
    GenericMeets (forcingProjectionGeneric P0 R0 π G) A0 ↔ GenericMeets G A1 :=
  ⟨agreement_generic_of_forces hsplit hG.1 hA1 hagree,
    agreement_forces_of_generic hR0 hsplit hG hA1 hagreeNeg⟩

end ZFVP
