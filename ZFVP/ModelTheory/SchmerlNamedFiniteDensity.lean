import ZFVP.ModelTheory.SchmerlNamedSeparationDensity
import ZFVP.ModelTheory.InternalFiniteOmissionFormulas
import ZFVP.ModelTheory.SchmerlCodedSourceBridge

/-! Every old source-finite set has a dense omission task over the whole
upper-bound background. The finite induction takes place in the source model. -/

namespace ZFVP.Schmerl
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem namedFiniteOmissionDense_dense (hAC : InternalChoice V) (hω : HasStandardOmega V)
    {D E j k a l : V} (hM : IsCodedZFModel (binaryRelationStructureCode D E))
    (hE : E ⊆ D ×ˢ D)
    (hj : j ∈ (ω : V) ^ D) (hji : Injective j)
    (hk : k ∈ (ω : V) ^ codedDirectedPosetIndex (binaryRelationStructureCode D E)) (hki : Injective k)
    (hdis : ∀ n ∈ range j, n ∉ range k) (ha : a ∈ D)
    (hfinite : codedUnary (binaryRelationStructureCode D E) (encodeMembershipFormula internallyFiniteFormula) a)
    (hl : l ∈ (ω : V)) :
    ForcingDense
      (namedFiniteConditions membershipLanguageCode (binaryRelationStructureCode D E) j
        (namedUpperBackground (binaryRelationStructureCode D E) j k))
      (reverseInclusionOrder (namedFiniteConditions membershipLanguageCode (binaryRelationStructureCode D E) j
        (namedUpperBackground (binaryRelationStructureCode D E) j k)))
      (namedFiniteOmissionDense
        (namedFiniteConditions membershipLanguageCode (binaryRelationStructureCode D E) j
          (namedUpperBackground (binaryRelationStructureCode D E) j k))
        (binaryRelationStructureCode D E) j a l) := by
  classical
  have hD : IsNonempty D := by simpa only [binaryRelationStructureCode_domain] using hM.valid.domain_nonempty
  let : Nonempty (BinaryRelationDomain D E) := binaryRelationDomain_nonempty hD
  let representation := binaryIdentityRepresentation hD hE
  let : (BinaryRelationDomain D E)↓[ℒₛₑₜ] ⊧* 𝗭𝗙 := representation.models_zf_of_isCodedZFModel hM
  let old : BinaryRelationDomain D E := ⟨a, ha⟩
  have hold : IsInternallyFinite old := (codedUnary_finite_iff hD old).mp hfinite
  refine ⟨namedFiniteOmissionDense_subset _ _ _ _ _, fun A hA ↦ ?_⟩
  obtain ⟨hAv, hAfin, hAf⟩ := (mem_namedFiniteConditions _ _ _ _ _).mp hA
  obtain ⟨N, _, _, _, hform⟩ := exists_finiteOmissionFormulas hω hD hj hji hk hki hdis hAfin hAv hl ha
  obtain ⟨p, indices, hinj, hi, hcoverI, _⟩ := exists_finiteUpperIndices hk hki N
  obtain ⟨B, Outside, Member, hΦ⟩ := hform p indices hi hcoverI
  choose δ ρ hδ hρ hdir using fun z ↦ codedDirectedPoset_sourceFormulas hω hD (hi z)
  have hblock := (finiteSource_iff_finiteBlock hAC hD hj hji hk hki hdis hAfin hAv
    indices hi hinj δ ρ hδ hρ (fun s ↦ B.Eval s id) (fun c hc ↦ (hΦ c hc).1)).mp hAf
  have hcover : ∀ s, B.Eval s id → Outside.Eval s id ∨ ∃ m ∈ old, Member.Eval (m :> s) id := by
    intro s hs
    obtain ⟨c, hc, rfl⟩ := exists_upperTupleAssignment hD indices hi hinj s
    exact (hΦ c hc).2.2.2 hs
  have hext (q : V) (hq : q ∈ namedFormulaSet membershipLanguageCode (ω : V))
      (Ψ : SetTheorySemiformula (BinaryRelationDomain D E) p)
      (hΨ : ∀ (c : V) (hc : c ∈ D ^ codedDirectedPosetIndex (binaryRelationStructureCode D E)),
        Ψ.Eval (fun z ↦ ⟨c ‘ (indices z), function_value_mem hc (hi z)⟩) id ↔
          ∃ f, ZFVP.SourceNaming (binaryRelationStructureCode D E) j f ∧
            (∀ i ∈ codedDirectedPosetIndex (binaryRelationStructureCode D E), f ‘ (k ‘ i) = c ‘ i) ∧
            (∀ r ∈ A, NamedHolds membershipLanguageCode (binaryRelationStructureCode D E) f r) ∧
            NamedHolds membershipLanguageCode (binaryRelationStructureCode D E) f q)
      (hΨblock : FiniteBlockEx δ ρ fun s ↦ Ψ.Eval s id) :
      A ∪ {q} ∈ namedFiniteConditions membershipLanguageCode (binaryRelationStructureCode D E) j
        (namedUpperBackground (binaryRelationStructureCode D E) j k) := by
    have hfin : IsInternallyFinite (A ∪ {q}) := internallyFinite_union hAfin (by
      simpa using internallyFinite_insert internallyFinite_empty q)
    have hsub : A ∪ {q} ⊆ namedFormulaSet membershipLanguageCode (ω : V) := by
      intro r hr
      rcases mem_union_iff.mp hr with hr | hr
      · exact hAv r hr
      · exact (mem_singleton_iff.mp hr) ▸ hq
    apply (mem_namedFiniteConditions _ _ _ _ _).mpr
    refine ⟨hsub, hfin, (finiteSource_iff_finiteBlock hAC hD hj hji hk hki hdis hfin hsub
      indices hi hinj δ ρ hδ hρ (fun s ↦ Ψ.Eval s id) ?_).mpr hΨblock⟩
    intro c hc
    rw [hΨ c hc]
    apply exists_congr
    intro f
    exact and_congr Iff.rfl (and_congr Iff.rfl (namedHolds_union_singleton _ _ _ _ _).symm)
  rcases rubin_finiteIndex_finite_cons_split δ ρ hdir B Outside Member hold hcover hblock with hOutside | ⟨m, hm, hMember⟩
  · let q := namedNegation membershipLanguageCode (namedMembershipEntry l (j ‘ a))
    have hq := namedNegation_mem membershipLanguageCode_valid (namedMembershipEntry_valid hl (function_value_mem hj ha))
    have hnew := hext q hq Outside (fun c hc ↦ (hΦ c hc).2.1) hOutside
    exact ⟨A ∪ {q}, (mem_namedFiniteOmissionDense _ _ _ _ _ _).mpr ⟨hnew, Or.inl (by simp [q])⟩,
      (pair_mem_reverseInclusionOrder _ _ _).mpr ⟨hnew, hA, fun _ hr ↦ mem_union_iff.mpr (Or.inl hr)⟩⟩
  · let q := namedEqualityEntry l (j ‘ m.val)
    let Ψ : SetTheorySemiformula (BinaryRelationDomain D E) p :=
      Rew.bind (&m :> fun z ↦ #z) Semiterm.fvar ▹ Member
    have heval (s : Fin p → BinaryRelationDomain D E) : Ψ.Eval s id ↔ Member.Eval (m :> s) id := by
      simp only [Ψ, Semiformula.eval_rew]
      have he : Semiterm.val (L := ℒₛₑₜ) s id ∘ (&m :> fun z ↦ #z) = m :> s := by
        funext z
        refine Fin.cases ?_ (fun i ↦ ?_) z <;> simp
      simpa only [Rew.bind_bvar, Rew.bind_fvar, Function.comp_def, Semiterm.val_fvar] using
        Iff.of_eq (congrArg (fun b ↦ Member.Eval b id) he)
    have hnew := hext q (namedEqualityEntry_valid hl (function_value_mem hj m.property)) Ψ
      (fun c hc ↦ (heval _).trans ((hΦ c hc).2.2.1 m)) (by simpa only [heval] using hMember)
    have hmtrace : m.val ∈ codedMemberTrace (binaryRelationStructureCode D E) a :=
      (codedMemberTrace_binary_iff hD ha).mpr ⟨m.property, hm⟩
    exact ⟨A ∪ {q}, (mem_namedFiniteOmissionDense _ _ _ _ _ _).mpr
      ⟨hnew, Or.inr ⟨m.val, hmtrace, by simp [q]⟩⟩,
      (pair_mem_reverseInclusionOrder _ _ _).mpr ⟨hnew, hA, fun _ hr ↦ mem_union_iff.mpr (Or.inl hr)⟩⟩

end ZFVP.Schmerl
