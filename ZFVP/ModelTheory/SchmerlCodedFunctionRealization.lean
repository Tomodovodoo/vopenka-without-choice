import ZFVP.ModelTheory.SchmerlCodedFunctionColors
import ZFVP.ModelTheory.SchmerlCodedFunctionFamilyTransport
import ZFVP.ModelTheory.SchmerlCodedFiniteDomainSelection

/-! The uniform function-tree sentence follows from the actual family of
colors and the original membership codes for preserved candidates. -/

set_option autoImplicit false

namespace ZFVP.BinaryRelationRepresentation
open LO LO.FirstOrder LO.FirstOrder.SetTheory Schmerl
open ZFVP.Infinitary (Formula)
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {W : Type*} [SetStructure W] [Nonempty W] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable (R : BinaryRelationRepresentation (V := V) W)

theorem infiniteSet_mem_iff (s : W) :
    (R.equiv s).val ∈ codedInfiniteSets R.code ↔ IsInternallyInfinite s := by
  rw [codedInfiniteSets, R.mem_unarySet_iff]
  simp

theorem mem_infiniteSets_iff (x : V) :
    x ∈ codedInfiniteSets R.code ↔ ∃ s : W, (R.equiv s).val = x ∧ IsInternallyInfinite s := by
  constructor
  · intro hx
    have hxD : x ∈ R.carrier := by
      simpa only [code, binaryRelationStructureCode_domain] using codedInfiniteSets_subset R.code x hx
    let s := R.equiv.symm ⟨x, hxD⟩
    have hs : (R.equiv s).val = x := congrArg Subtype.val (R.equiv.apply_symm_apply _)
    exact ⟨s, hs, (R.infiniteSet_mem_iff s).mp (hs.symm ▸ hx)⟩
  · rintro ⟨s, rfl, hs⟩
    exact (R.infiniteSet_mem_iff s).mpr hs

variable {c C H : V}
variable (hc : IsInternalCofinalStrictChain (hartogsNumber (ω : V))
  (codedOrdinals R.code) (codedOrdinalOrder R.code) c)
variable (hC : IsCodedFiniteDomainFamily R.code (hartogsNumber (ω : V)) C)
variable (hH : ∀ s ∈ codedInfiniteSets R.code,
  H ‘ s ∈ (ω : V) ^ codedSelectedFunctionNodes R.code s (hartogsNumber (ω : V)) (C ‘ s) ∧
    InternallyWeakSpecialization (codedSelectedFunctionNodes R.code s (hartogsNumber (ω : V)) (C ‘ s))
      (codedSelectedFunctionOrder R.code s (hartogsNumber (ω : V)) (C ‘ s)) (H ‘ s))

include hc hC hH in
theorem functionTreeFamilySentenceWithQ_of_candidate_codes
    (hcodes : ∀ s : W, IsInternallyInfinite s → ∀ g : V, ∀ hg : g ∈ R.carrier ^ R.carrier,
      InternallyWeakSpecialization
        (codedSelectedFunctionNodes R.code (R.equiv s).val (hartogsNumber (ω : V)) (C ‘ (R.equiv s).val))
        (codedSelectedFunctionOrder R.code (R.equiv s).val (hartogsNumber (ω : V)) (C ‘ (R.equiv s).val)) g →
      ∀ b : W, b ∈ finitePartialFunctions s ((2 : ℕ) : W) →
        (R.equiv (domain b)).val ∈ range (C ‘ (R.equiv s).val) →
        (∀ d : W, (R.equiv d).val ∈ range (C ‘ (R.equiv s).val) → ∃ p : W,
          functionFilterCandidate s (fun a ↦ (R.equiv a).val ∈ range (C ‘ (R.equiv s).val))
            (fun x y ↦ R.representedColor hg x = R.representedColor hg y) b p ∧ d ⊆ domain p) →
        ∃ m : W, ∀ p : W, p ∈ m ↔ functionFilterCandidate s
          (fun a ↦ (R.equiv a).val ∈ range (C ‘ (R.equiv s).val))
          (fun x y ↦ R.representedColor hg x = R.representedColor hg y) b p)
    {k : V} (hk : k ∈ R.carrier ^ R.carrier) :
    ∃ G : V, ∃ hG : G ∈ R.carrier ^ (R.carrier ×ˢ R.carrier),
      @Formula.EvalWithQ deadEndLanguage W
        (R.representedDeadEndExpansion hk hG c (codedSelectedDomainRelation R.code C)) R.representedQ 0
        (functionTreeFamilySentence deadEndSetEmbedding functionSelected functionColor) ![] := by
  let I := codedInfiniteSets R.code
  let T := codedFunctionTreeFamily R.code (hartogsNumber (ω : V)) C
  have hHfun : ∀ s ∈ I, H ‘ s ∈ (ω : V) ^ (T ‘ s) := by
    intro s hs
    simpa only [T, value_codedFunctionTreeFamily hs] using (hH s hs).1
  let G := codedFunctionColorGraph R.carrier I T c H
  have hG : G ∈ R.carrier ^ (R.carrier ×ˢ R.carrier) := R.codedFunctionColorGraph_function hc hHfun
  let S := R.representedDeadEndExpansion hk hG c (codedSelectedDomainRelation R.code C)
  refine ⟨G, hG, ?_⟩
  apply (evalWithQ_functionTreeFamilySentence deadEndSetEmbedding S
    (R.representedDeadEndExpansion_reduct hk hG c _) R.representedQ functionSelected functionColor).mpr
  intro s hs
  have hsI : (R.equiv s).val ∈ I := (R.infiniteSet_mem_iff s).mpr hs
  have hcD := hC.2 (R.equiv s).val hsI
  let row := codedFunctionColorRow R.carrier I T c H (R.equiv s).val
  have hrow : row ∈ R.carrier ^ R.carrier := R.codedFunctionColorRow_function hc hHfun (R.equiv s).val
  let f := R.representedColor hrow
  have hselected (d : W) : @Formula.Eval deadEndLanguage W S 2 functionSelected ![s, d] ↔
      (R.equiv d).val ∈ range (C ‘ (R.equiv s).val) :=
    pair_mem_codedSelectedDomainRelation_of_mem hC hsI (R.equiv d).val
  have hselected_eq : (fun d ↦ @Formula.Eval deadEndLanguage W S 2 functionSelected ![s, d]) =
      (fun d ↦ (R.equiv d).val ∈ range (C ‘ (R.equiv s).val)) := funext fun d ↦ propext (hselected d)
  have hcolor (a x : W) : @Formula.Eval deadEndLanguage W S 3 functionColor ![s, a, x] ↔ a = f x := by
    change a = R.representedFunctionColor hG s x ↔ a = f x
    rw [R.representedFunctionColor_eq_row hc hHfun s x]
  have hTD : T ‘ (R.equiv s).val ⊆ R.carrier := by
    rw [value_codedFunctionTreeFamily hsI]
    intro x hx
    simpa only [code, binaryRelationStructureCode_domain] using
      ((mem_codedParameterSet _ _ _ _).mp ((mem_codedSelectedFunctionNodes _ _ _ _ _).mp hx).1).1
  have hweak : InternallyWeakSpecialization
      (codedSelectedFunctionNodes R.code (R.equiv s).val (hartogsNumber (ω : V)) (C ‘ (R.equiv s).val))
      (codedSelectedFunctionOrder R.code (R.equiv s).val (hartogsNumber (ω : V)) (C ‘ (R.equiv s).val)) row := by
    have hh := R.codedFunctionColorRow_internalWeak hc hHfun hsI hTD
      (S := codedSelectedFunctionOrder R.code (R.equiv s).val (hartogsNumber (ω : V)) (C ‘ (R.equiv s).val))
    rw [value_codedFunctionTreeFamily hsI] at hh
    exact hh (hH (R.equiv s).val hsI).2
  apply functionTreeDataClause_of_semanticDataWithQ deadEndSetEmbedding S
    (R.representedDeadEndExpansion_reduct hk hG c _) R.representedQ
    (by trivial) (by trivial) s f hcolor
  · rw [hselected_eq]
    exact R.finiteDomainChain_selectedDomainClausesWithQ hcD
  · exact R.codedFunctionColorRow_not_Q hc hHfun (R.equiv s).val
  · intro x y z hx hdx hy hdy hz hdz hxy hxz hexy hexz
    exact R.representedColor_functionWeak s hcD hrow hweak x y z hx ((hselected _).mp hdx)
      hy ((hselected _).mp hdy) hz ((hselected _).mp hdz) hxy hxz hexy hexz
  · intro b hb hdb hcof
    have hcof' := hcof
    rw [hselected_eq] at hcof'
    simp only [hselected] at hcof'
    obtain ⟨m, hm⟩ := hcodes s hs row hrow hweak b hb ((hselected _).mp hdb) hcof'
    refine ⟨m, ?_⟩
    simpa only [hselected_eq] using hm

variable {U : Type*} [SetStructure U] [Nonempty U] [U↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

include hc hC in
theorem endExtension_functionTreeFamilySentenceWithQ (j : MembershipEndExtension V U)
    (hκ : j (hartogsNumber (ω : V)) = hartogsNumber (ω : U))
    (hω : HasStandardOmega V) (hRubin : IsCodedRubin R.code (hartogsNumber (ω : V)))
    (hpres : ∀ s : W, IsInternallyInfinite s → ∀ B : U,
      IsInternalCofinalBranch
        (j (codedSelectedFunctionNodes R.code (R.equiv s).val (hartogsNumber (ω : V)) (C ‘ (R.equiv s).val)))
        (j (codedSelectedFunctionOrder R.code (R.equiv s).val (hartogsNumber (ω : V)) (C ‘ (R.equiv s).val)))
        (j (hartogsNumber (ω : V)))
        (j (codedSelectedFunctionRank R.code (R.equiv s).val (hartogsNumber (ω : V)) (C ‘ (R.equiv s).val))) B →
      ∃ A : V, IsInternalCofinalBranch
        (codedSelectedFunctionNodes R.code (R.equiv s).val (hartogsNumber (ω : V)) (C ‘ (R.equiv s).val))
        (codedSelectedFunctionOrder R.code (R.equiv s).val (hartogsNumber (ω : V)) (C ‘ (R.equiv s).val))
        (hartogsNumber (ω : V))
        (codedSelectedFunctionRank R.code (R.equiv s).val (hartogsNumber (ω : V)) (C ‘ (R.equiv s).val)) A ∧ j A = B)
    {H : U} (hH : ∀ s ∈ codedInfiniteSets (R.endExtension j).code,
      H ‘ s ∈ (ω : U) ^ codedSelectedFunctionNodes (R.endExtension j).code s (hartogsNumber (ω : U)) ((j C) ‘ s) ∧
        InternallyWeakSpecialization
          (codedSelectedFunctionNodes (R.endExtension j).code s (hartogsNumber (ω : U)) ((j C) ‘ s))
          (codedSelectedFunctionOrder (R.endExtension j).code s (hartogsNumber (ω : U)) ((j C) ‘ s)) (H ‘ s))
    {k : U} (hk : k ∈ (R.endExtension j).carrier ^ (R.endExtension j).carrier) :
    ∃ G : U, ∃ hG : G ∈ (R.endExtension j).carrier ^
        ((R.endExtension j).carrier ×ˢ (R.endExtension j).carrier),
      @Formula.EvalWithQ deadEndLanguage W
        ((R.endExtension j).representedDeadEndExpansion hk hG (j c)
          (codedSelectedDomainRelation (R.endExtension j).code (j C)))
        (R.endExtension j).representedQ 0
        (functionTreeFamilySentence deadEndSetEmbedding functionSelected functionColor) ![] := by
  have hc' : IsInternalCofinalStrictChain (hartogsNumber (ω : U))
      (codedOrdinals (R.endExtension j).code) (codedOrdinalOrder (R.endExtension j).code) (j c) := by
    simpa only [hκ] using R.endExtension_cofinalChain j hc
  have hC' : IsCodedFiniteDomainFamily (R.endExtension j).code (hartogsNumber (ω : U)) (j C) := by
    simpa only [hκ] using R.endExtension_finiteDomainFamily j hC
  apply (R.endExtension j).functionTreeFamilySentenceWithQ_of_candidate_codes hc' hC' hH ?_ hk
  intro s hs g hg hweak b hb hdb hcof
  have hcD := hC.2 (R.equiv s).val ((R.infiniteSet_mem_iff s).mpr hs)
  have heC : (j C) ‘ ((R.endExtension j).equiv s).val = j (C ‘ (R.equiv s).val) := by
    rw [R.endExtension_equiv_val, j.map_value_total]
  rw [heC] at hdb hcof ⊢
  rw [heC, ← hκ, R.endExtension_equiv_val j s] at hweak
  exact R.endExtension_functionFilterCandidate_has_code s hcD j hω hRubin
    (hpres s hs) hg hweak hb hdb hcof

end ZFVP.BinaryRelationRepresentation
