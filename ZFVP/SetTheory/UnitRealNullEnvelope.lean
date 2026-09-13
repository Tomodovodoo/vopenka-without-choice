import ZFVP.SetTheory.BinaryRealEnvelope
import ZFVP.SetTheory.BinaryRealNullImages

/-! Actual G-delta null-excess envelopes on the real unit interval. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem unitReal_nullGDeltaEnvelope {A : V} (hA : A ⊆ unitReals V)
    (hLM : IsLebesgueMeasurable (binaryPreimage A)) : HasRealNullGDeltaEnvelope A := by
  obtain ⟨g, hg, hBg, hN⟩ := hLM
  have hNC : (gDelta g \ binaryPreimage A) ⊆ cantorSpace V := by
    intro c hc
    exact ((mem_gDelta_iff _ _).mp (mem_sdiff_iff.mp hc).1).1
  refine ⟨binaryRealEnvelopeCode g, binaryRealEnvelopeCode_mem g, ?_, ?_⟩
  · intro x hx
    apply (binaryRealEnvelope_iff hg).mpr
    refine ⟨hA x hx, fun c hc hcx ↦ hBg c ?_⟩
    exact (mem_binaryPreimage_iff _ _).mpr ⟨hc, hcx.symm ▸ hx⟩
  · apply realNull_subset (binaryImage_realNull hNC hN)
    intro x hx
    obtain ⟨hxg, hxA⟩ := mem_sdiff_iff.mp hx
    obtain ⟨hxU, hfiber⟩ := (binaryRealEnvelope_iff hg).mp hxg
    obtain ⟨c, hc, hcx⟩ := binaryReal_surjective hxU
    refine (mem_binaryImage_iff _ _).mpr ⟨c, mem_sdiff_iff.mpr ⟨hfiber c hc hcx, ?_⟩, hcx⟩
    intro hcB
    exact hxA (hcx ▸ ((mem_binaryPreimage_iff _ _).mp hcB).2)

theorem allUnitReal_nullGDeltaEnvelope_of_cantor (hLM : AllLebesgueMeasurable V) :
    ∀ A : V, A ⊆ unitReals V → HasRealNullGDeltaEnvelope A := by
  intro A hA
  apply unitReal_nullGDeltaEnvelope hA
  apply hLM
  exact fun _ h ↦ ((mem_binaryPreimage_iff _ _).mp h).1

end ZFVP
