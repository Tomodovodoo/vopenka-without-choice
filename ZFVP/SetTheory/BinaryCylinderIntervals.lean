import ZFVP.SetTheory.BinaryGreedySurjection
import ZFVP.SetTheory.BinaryPrefixSeparation
import ZFVP.SetTheory.RealIntervalBasics

/-! The interior of a prefix interval has precisely that binary prefix. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem binaryInterval_subset_unit {c n : V} (hc : c ∈ cantorSpace V) (hn : n ∈ (ω : V)) :
    realInterval (binaryValue c n) (binaryUpper c n) ⊆ unitReals V := by
  intro x hx
  obtain ⟨hxCut, hlo, hup⟩ := (mem_realInterval_iff _ _ _).mp hx
  let N : InternalNatural V := ⟨n, hn⟩
  have hl : rationalCut (rationalZero V) ⊆ rationalCut (binaryValue c n) :=
    InternalRational.rationalCut_mono (InternalRational.binaryApprox_nonneg c hc N)
  have hu : rationalCut (binaryUpper c n) ⊆ rationalCut (rationalOne V) :=
    InternalRational.rationalCut_mono (InternalRational.binaryApprox_upper_le_one c hc N)
  exact (mem_unitReals_iff _).mpr ⟨hxCut, subset_trans hl hlo.1, subset_trans hup.1 hu⟩

theorem binaryInterval_nonempty {c n : V} (hc : c ∈ cantorSpace V) (hn : n ∈ (ω : V)) :
    IsNonempty (realInterval (binaryValue c n) (binaryUpper c n)) := by
  have hl := binaryValue_mem hc hn
  have hu := binaryUpper_mem hc hn
  obtain ⟨q, hq, hlq, hqu⟩ := internalRational_dense hl hu (binaryValue_lt_upper hc hn hn)
  exact ⟨rationalCut q, (mem_realInterval_iff _ _ _).mpr ⟨rationalCut_isCut hq,
    (rationalCut_lt_iff hl hq).mpr hlq, (rationalCut_lt_iff hq hu).mpr hqu⟩⟩

theorem binaryInterval_preimage_prefix {c d n : V} (hc : c ∈ cantorSpace V)
    (hd : d ∈ cantorSpace V) (hn : n ∈ (ω : V))
    (hx : binaryReal d ∈ realInterval (binaryValue c n) (binaryUpper c n)) :
    c ↾ n = d ↾ n := by
  obtain ⟨_, hlow, hupp⟩ := (mem_realInterval_iff _ _ _).mp hx
  let N : InternalNatural V := ⟨n, hn⟩
  rcases lt_trichotomy (InternalNatural.binaryNumeratorOf c hc N)
      (InternalNatural.binaryNumeratorOf d hd N) with hcd | he | hdc
  · have hg : rationalCut (binaryUpper c n) ⊆ rationalCut (binaryValue d n) :=
      InternalRational.rationalCut_mono (InternalRational.binaryApprox_gap hc hd N hcd)
    exact (dedekindLT_irrefl _ (dedekindLT_of_lt_of_subset hupp
      (subset_trans hg (binaryReal_lower hn)))).elim
  · exact binaryPrefix_eq_of_numerator_eq hc hd hn (congrArg Subtype.val he)
  · have hg : rationalCut (binaryUpper d n) ⊆ rationalCut (binaryValue c n) :=
      InternalRational.rationalCut_mono (InternalRational.binaryApprox_gap hd hc N hdc)
    exact (dedekindLT_irrefl _ (dedekindLT_of_lt_of_subset hlow
      (subset_trans (binaryReal_upper hd hn) hg))).elim

theorem binaryInterval_surjective_prefix {c n x : V} (hc : c ∈ cantorSpace V)
    (hn : n ∈ (ω : V)) (hx : x ∈ realInterval (binaryValue c n) (binaryUpper c n)) :
    ∃ d ∈ cantorSpace V, binaryReal d = x ∧ c ↾ n ⊆ d := by
  obtain ⟨d, hd, rfl⟩ := binaryReal_surjective (binaryInterval_subset_unit hc hn x hx)
  refine ⟨d, hd, rfl, ?_⟩
  rw [binaryInterval_preimage_prefix hc hd hn hx]
  exact restrict_subset _ _

end ZFVP
