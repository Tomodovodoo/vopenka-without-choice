import ZFVP.ModelTheory.SchmerlCodedSourceSimultaneousForcing
import ZFVP.ModelTheory.SchmerlCodedFunctionRealization
import ZFVP.ModelTheory.SchmerlCodedClassRealization
import ZFVP.ModelTheory.SchmerlCodedFiniteSmallWithQ
import ZFVP.ModelTheory.SchmerlInfinitaryDeadEndWithQ

/-! The same forcing extension realizes all clauses of the fixed weakly Rubin
sentence on the faithful representation of the source model. -/

set_option autoImplicit false

namespace ZFVP.BinaryRelationRepresentation
open LO LO.FirstOrder LO.FirstOrder.SetTheory Schmerl
open ZFVP.Infinitary (Formula)
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {W : Type*} [SetStructure W] [Nonempty W] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable (R : BinaryRelationRepresentation (V := V) W)

theorem weaklyRubin_realization_of_specialization (hω : HasStandardOmega V)
    {c C : V}
    (hc : IsInternalCofinalStrictChain (hartogsNumber (ω : V))
      (codedOrdinals R.code) (codedOrdinalOrder R.code) c)
    (hC : IsCodedFiniteDomainFamily R.code (hartogsNumber (ω : V)) C)
    (hRubin : IsCodedRubin R.code (hartogsNumber (ω : V))) (hsmall : IsCodedFinSmall R.code)
    {F : ForcingContext V} {f H : F.Model} (hspec : CodedSourceSpecialization R.code c C F f H) :
    ∃ k G : F.Model,
      ∃ hk : k ∈ (R.endExtension F.checkEmbedding).carrier ^ (R.endExtension F.checkEmbedding).carrier,
      ∃ hG : G ∈ (R.endExtension F.checkEmbedding).carrier ^
          ((R.endExtension F.checkEmbedding).carrier ×ˢ (R.endExtension F.checkEmbedding).carrier),
      @Formula.EvalWithQ deadEndLanguage W
        ((R.endExtension F.checkEmbedding).representedDeadEndExpansion hk hG (F.check c)
          (codedSelectedDomainRelation (R.endExtension F.checkEmbedding).code (F.check C)))
        (R.endExtension F.checkEmbedding).representedQ 0 weaklyRubinSentence ![] := by
  let j := F.checkEmbedding
  let R' := R.endExtension j
  have hκ : j (hartogsNumber (ω : V)) = hartogsNumber (ω : F.Model) := hspec.hartogs
  have hf := hspec.class_color
  have hwf := hspec.class_weak
  change f ∈ (ω : F.Model) ^ j (codedSelectedClassNodes R.code (hartogsNumber (ω : V)) c) at hf
  change InternallyWeakSpecialization (j (codedSelectedClassNodes R.code (hartogsNumber (ω : V)) c))
    (j (codedSelectedClassOrder R.code (hartogsNumber (ω : V)) c)) f at hwf
  rw [R.endExtension_codedSelectedClassNodes j, hκ] at hf
  rw [R.endExtension_codedSelectedClassNodes j, R.endExtension_codedSelectedClassOrder j, hκ] at hwf
  obtain ⟨k, hk, hclass⟩ := R.endExtension_classTreeSentenceWithQ hc j hκ hRubin
    hspec.class_branches hω hf hwf
  have hH : ∀ s ∈ codedInfiniteSets R'.code,
      H ‘ s ∈ (ω : F.Model) ^ codedSelectedFunctionNodes R'.code s (hartogsNumber (ω : F.Model)) ((j C) ‘ s) ∧
        InternallyWeakSpecialization
          (codedSelectedFunctionNodes R'.code s (hartogsNumber (ω : F.Model)) ((j C) ‘ s))
          (codedSelectedFunctionOrder R'.code s (hartogsNumber (ω : F.Model)) ((j C) ‘ s)) (H ‘ s) := by
    intro s hs
    rw [← R.endExtension_codedInfiniteSets j] at hs
    obtain ⟨a, ha, rfl⟩ := j.endExtension _ s hs
    have haD : a ∈ R.carrier := by
      simpa only [code, binaryRelationStructureCode_domain] using codedInfiniteSets_subset R.code a ha
    have hh := hspec.function_colors a ha
    change H ‘ (j a) ∈ (ω : F.Model) ^ j (codedSelectedFunctionNodes R.code a (hartogsNumber (ω : V)) (C ‘ a)) ∧
      InternallyWeakSpecialization (j (codedSelectedFunctionNodes R.code a (hartogsNumber (ω : V)) (C ‘ a)))
        (j (codedSelectedFunctionOrder R.code a (hartogsNumber (ω : V)) (C ‘ a))) (H ‘ (j a)) at hh
    rw [R.endExtension_codedSelectedFunctionNodes j a haD,
      R.endExtension_codedSelectedFunctionOrder j a haD, hκ, j.map_value_total] at hh
    exact hh
  have hpres : ∀ s : W, IsInternallyInfinite s → ∀ B : F.Model,
      IsInternalCofinalBranch
        (j (codedSelectedFunctionNodes R.code (R.equiv s).val (hartogsNumber (ω : V)) (C ‘ (R.equiv s).val)))
        (j (codedSelectedFunctionOrder R.code (R.equiv s).val (hartogsNumber (ω : V)) (C ‘ (R.equiv s).val)))
        (j (hartogsNumber (ω : V)))
        (j (codedSelectedFunctionRank R.code (R.equiv s).val (hartogsNumber (ω : V)) (C ‘ (R.equiv s).val))) B →
      ∃ A : V, IsInternalCofinalBranch
        (codedSelectedFunctionNodes R.code (R.equiv s).val (hartogsNumber (ω : V)) (C ‘ (R.equiv s).val))
        (codedSelectedFunctionOrder R.code (R.equiv s).val (hartogsNumber (ω : V)) (C ‘ (R.equiv s).val))
        (hartogsNumber (ω : V))
        (codedSelectedFunctionRank R.code (R.equiv s).val (hartogsNumber (ω : V)) (C ‘ (R.equiv s).val)) A ∧ j A = B :=
    fun s hs ↦ hspec.function_branches (R.equiv s).val ((R.infiniteSet_mem_iff s).mpr hs)
  obtain ⟨G, hG, hfunctions⟩ := R.endExtension_functionTreeFamilySentenceWithQ hc hC j hκ hω hRubin hpres hH hk
  refine ⟨k, G, hk, hG, ?_⟩
  apply weaklyRubinSentence_of_clausesWithQ
    (fun x ↦ (R'.equiv x).val ∈ range (j c)) (R'.representedColor hk)
    (fun s d ↦ ⟨(R'.equiv s).val, (R'.equiv d).val⟩ₖ ∈ codedSelectedDomainRelation R'.code (j C))
    (R'.representedFunctionColor hG) R'.representedQ hclass
  · exact (evalWithQ_functionTreeFamilySentence deadEndSetEmbedding
      (R'.representedDeadEndExpansion hk hG (j c) (codedSelectedDomainRelation R'.code (j C)))
      rfl R'.representedQ functionSelected functionColor).mp hfunctions
  · exact R.endExtension_representedQ_finiteSmall j hsmall

end ZFVP.BinaryRelationRepresentation
