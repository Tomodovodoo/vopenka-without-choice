import ZFVP.ModelTheory.SchmerlCodedWeaklyRubinRealization
import ZFVP.ModelTheory.SchmerlCodedDeadEndLanguageTransport
import ZFVP.ModelTheory.SchmerlCodedDeadEndEquality

/-! The forcing construction returns an actual coded expansion, independently
of any chosen syntax fragment. Fragment truth is a consequence of its semantics. -/

set_option autoImplicit false

namespace ZFVP.Schmerl
open LO LO.FirstOrder LO.FirstOrder.SetTheory
open ZFVP.Infinitary (Formula)
open ZFVP.Infinitary.Internal
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

structure CodedWeaklyRubinExpansion (D E : V) where
  carrier_nonempty : IsNonempty D
  relation_subset : E ⊆ D ×ˢ D
  classSelection : V
  classColor : V
  selectedDomains : V
  functionColor : V
  classColor_total : classColor ∈ D ^ D
  functionColor_total : functionColor ∈ D ^ (D ×ˢ D)
  realizes : @Formula.EvalWithQ deadEndLanguage
    (CodedDomain (codedDeadEndExpansion D E classSelection classColor selectedDomains functionColor))
    (codedFoundationStructure (codedDeadEndExpansion_valid carrier_nonempty E classSelection classColor selectedDomains functionColor)
      (fun {k} ↦ deadEndFunctionSymbol (V := V) (k := k)) deadEndRelationSymbol
      (fun _ f ↦ deadEndFunctionSymbol_valid f))
    (InternalQ (codedDeadEndExpansion D E classSelection classColor selectedDomains functionColor))
    0 weaklyRubinSentence ![]

namespace CodedWeaklyRubinExpansion
variable {D E : V} (A : CodedWeaklyRubinExpansion D E)

noncomputable def code : V :=
  codedDeadEndExpansion D E A.classSelection A.classColor A.selectedDomains A.functionColor

theorem valid : IsStructureCode (deadEndLanguageCode : V) A.code :=
  codedDeadEndExpansion_valid A.carrier_nonempty E A.classSelection A.classColor A.selectedDomains A.functionColor

theorem holds (hω : HasStandardOmega V)
    {H : V} {C : {n : ℕ} → Infinitary.Formula deadEndLanguage n → V}
    {B : Set (Σ n, Infinitary.Formula deadEndLanguage n)}
    (hcode : IsFragmentCoding (deadEndLanguageCode : V) H
      (fun {k} ↦ deadEndFunctionSymbol (V := V) (k := k)) deadEndRelationSymbol C B)
    (hroot : ⟨0, weaklyRubinSentence⟩ ∈ B) :
    Holds (deadEndLanguageCode : V) H A.code 0 (C weaklyRubinSentence) ∅ := by
  have hh := (hcode.holds_iff_evalWithQ hω A.valid (fun _ f ↦ deadEndFunctionSymbol_valid f)
    (fun _ r ↦ deadEndRelationSymbol_valid r) weaklyRubinSentence hroot
    (![] : Fin 0 → CodedDomain A.code)).mpr A.realizes
  simpa [standardTuple] using hh

end CodedWeaklyRubinExpansion

theorem IsCodedRubinFinSmallSource.exists_weaklyRubin_expansion [Countable V]
    (hAC : InternalChoice V) (hω : HasStandardOmega V) {M : V} (hsource : IsCodedRubinFinSmallSource M) :
    ∃ F : ForcingContext V, InternalChoice F.Model ∧
      F.check (hartogsNumber (ω : V)) = hartogsNumber (ω : F.Model) ∧
      ∃ D E : V, M = binaryRelationStructureCode D E ∧
        Nonempty (CodedWeaklyRubinExpansion (F.check D) (F.check E)) := by
  obtain ⟨c, C, hc, hC, F, f, H, hspec⟩ := hsource.exists_simultaneous_specialization hAC
  obtain ⟨⟨D, E, rfl, hE⟩, hZF, _, hRubin, hsmall⟩ := hsource
  have hD : IsNonempty D := by simpa only [binaryRelationStructureCode_domain] using hZF.valid.domain_nonempty
  let R := binaryIdentityRepresentation hD hE
  let : Nonempty (BinaryRelationDomain D E) := binaryRelationDomain_nonempty hD
  let : (BinaryRelationDomain D E)↓[ℒₛₑₜ] ⊧* 𝗭𝗙 := R.models_zf_of_isCodedZFModel hZF
  let j := F.checkEmbedding
  let R' := R.endExtension j
  obtain ⟨k, G, hk, hG, hreal⟩ := R.weaklyRubin_realization_of_specialization hω hc hC hRubin hsmall hspec
  let S := codedSelectedDomainRelation R'.code (j C)
  have hcoded := (R'.codedDeadEndExpansion_evalWithQ hk hG (j c) S weaklyRubinSentence ![]).mp hreal
  have he : R'.deadEndExpansionEquiv (g := k) (G := G) (j c) S ∘
      (![] : Fin 0 → BinaryRelationDomain D E) = ![] := funext fun i ↦ i.elim0
  rw [he] at hcoded
  exact ⟨F, hspec.choice, hspec.hartogs, D, E, rfl,
    ⟨⟨R'.carrier_nonempty, R'.relation_subset, range (j c), k, S, G, hk, hG, hcoded⟩⟩⟩

end ZFVP.Schmerl
