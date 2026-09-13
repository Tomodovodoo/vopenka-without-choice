import ZFVP.ModelTheory.ForcingModelPairs
import ZFVP.SetTheory.ForcingSequenceNames
import ZFVP.SetTheory.EndExtensionWellOrdering

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace ForcingContext

noncomputable def sequenceValue (S : ForcingContext V) (s : V) (hs : IsNameSequence S.P s) : S.Model :=
  S.ofName ⟨sequenceName S.one s, sequenceName_isName S.top.1 hs⟩

theorem mem_sequenceValue (S : ForcingContext V) (s : V) (hs : IsNameSequence S.P s) (z : S.Model) :
    z ∈ S.sequenceValue s hs ↔ ∃ i : V, ∃ hi : i ∈ domain s,
      z = ⟨S.check i, S.ofName ⟨s ‘ i, hs i hi⟩⟩ₖ := by
  have hv (i : V) (hi : i ∈ domain s) :
      S.ofName ⟨orderedPairName S.one (checkName S.one i) (s ‘ i),
        orderedPairName_isName S.top.1 (checkName_isName S.top.1 i) (hs i hi)⟩ =
        ⟨S.check i, S.ofName ⟨s ‘ i, hs i hi⟩⟩ₖ :=
    S.of_orderedPair ⟨checkName S.one i, checkName_isName S.top.1 i⟩ ⟨s ‘ i, hs i hi⟩
  rw [sequenceValue, S.mem_ofName_iff]
  constructor
  · rintro ⟨σ, p, _, hσp, hz⟩
    obtain ⟨i, hi, he⟩ := (mem_sequenceName _ _ _).mp hσp
    refine ⟨i, hi, hz.trans ?_⟩
    rw [← hv i hi]
    exact congrArg S.ofName (Subtype.ext (kpair_iff.mp he).1)
  · rintro ⟨i, hi, rfl⟩
    exact ⟨⟨orderedPairName S.one (checkName S.one i) (s ‘ i),
      orderedPairName_isName S.top.1 (checkName_isName S.top.1 i) (hs i hi)⟩,
      S.one, externalForcingFilter_top S.generic.1 S.top,
      (mem_sequenceName _ _ _).mpr ⟨i, hi, rfl⟩, (hv i hi).symm⟩

theorem sequenceValue_mem_function (S : ForcingContext V) (s : V) (hs : IsNameSequence S.P s)
    {A : S.Model} (hA : ∀ i : V, ∀ hi : i ∈ domain s, S.ofName ⟨s ‘ i, hs i hi⟩ ∈ A) :
    S.sequenceValue s hs ∈ A ^ S.check (domain s) := by
  apply mem_function.intro
  · intro z hz
    obtain ⟨i, hi, rfl⟩ := (S.mem_sequenceValue s hs z).mp hz
    exact kpair_mem_iff.mpr ⟨(S.check_mem_iff _ _).mpr hi, hA i hi⟩
  · intro x hx
    obtain ⟨i, hi, rfl⟩ := (S.mem_check_iff (domain s) x).mp hx
    refine ⟨S.ofName ⟨s ‘ i, hs i hi⟩, (S.mem_sequenceValue s hs _).mpr ⟨i, hi, rfl⟩, ?_⟩
    intro y hy
    obtain ⟨j, hj, he⟩ := (S.mem_sequenceValue s hs _).mp hy
    obtain ⟨hij, hyj⟩ := kpair_iff.mp he
    obtain rfl := (S.check_eq_iff i j).mp hij
    exact hyj

instance sequenceValue_isFunction (S : ForcingContext V) (s : V) (hs : IsNameSequence S.P s) :
    IsFunction (S.sequenceValue s hs) := by
  apply IsFunction.of_mem (S.sequenceValue_mem_function s hs (A := range (S.sequenceValue s hs)) ?_)
  intro i hi
  exact mem_range_of_kpair_mem ((S.mem_sequenceValue s hs _).mpr ⟨i, hi, rfl⟩)

theorem sequenceValue_domain (S : ForcingContext V) (s : V) (hs : IsNameSequence S.P s) :
    domain (S.sequenceValue s hs) = S.check (domain s) := by
  apply domain_eq_of_mem_function (S.sequenceValue_mem_function s hs (A := range (S.sequenceValue s hs)) ?_)
  intro i hi
  exact mem_range_of_kpair_mem ((S.mem_sequenceValue s hs _).mpr ⟨i, hi, rfl⟩)

theorem sequenceValue_value (S : ForcingContext V) (s : V) (hs : IsNameSequence S.P s)
    {i : V} (hi : i ∈ domain s) :
    (S.sequenceValue s hs) ‘ (S.check i) = S.ofName ⟨s ‘ i, hs i hi⟩ :=
  value_eq_of_kpair_mem ((S.mem_sequenceValue s hs _).mpr ⟨i, hi, rfl⟩)

theorem sequenceValue_restrict (S : ForcingContext V) {s A : V} [IsFunction s]
    (hs : IsNameSequence S.P s) (hA : A ⊆ domain s) :
    S.sequenceValue (s ↾ A) (hs.restrict hA) = (S.sequenceValue s hs) ↾ (S.check A) := by
  have hsr : s ↾ A ∈ (range s) ^ A :=
    function_restrict_mem (IsFunction.mem_function s) hA
  have hd : domain (s ↾ A) = A := domain_eq_of_mem_function hsr
  have hSc : S.check A ⊆ domain (S.sequenceValue s hs) := by
    rw [S.sequenceValue_domain]
    exact (S.checkEmbedding.subset_iff _ _).mpr hA
  have ht : (S.sequenceValue s hs) ↾ (S.check A) ∈ range (S.sequenceValue s hs) ^ (S.check A) :=
    function_restrict_mem (IsFunction.mem_function (S.sequenceValue s hs)) hSc
  have := IsFunction.of_mem ht
  apply functions_eq_of_domain_values
  · rw [S.sequenceValue_domain, hd, domain_eq_of_mem_function ht]
  · intro a ha
    rw [S.sequenceValue_domain, hd] at ha
    obtain ⟨i, hi, rfl⟩ := (S.mem_check_iff A a).mp ha
    rw [S.sequenceValue_value _ _ (hd.symm ▸ hi),
      value_restrict (hSc _ ((S.check_mem_iff _ _).mpr hi)) ((S.check_mem_iff _ _).mpr hi),
      S.sequenceValue_value _ _ (hA i hi)]
    exact congrArg S.ofName (Subtype.ext (value_restrict (hA i hi) hi))

end ForcingContext
end ZFVP
