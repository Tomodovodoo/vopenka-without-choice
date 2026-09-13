import ZFVP.ModelTheory.SchmerlNamedRefutationTransport
import ZFVP.ModelTheory.SchmerlNamedWeaklyRubinRealization
import ZFVP.ModelTheory.SchmerlForcedWeaklyRubinConstruction
import ZFVP.ModelTheory.CodedBinaryElementaryMap

set_option autoImplicit false
namespace ZFVP.Schmerl
open LO LO.FirstOrder LO.FirstOrder.SetTheory
open ZFVP.Infinitary.Internal
universe u
variable {V : Type u} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [Countable V]
variable {M : Type} [SetStructure M] [Nonempty M]

/-- The forced expansion, with the preserved original names, contradicts a
refutation of the named theory. Every forcing input is supplied by the coded model. -/
theorem NamedDeadEndRefutationSupport.false_of_forcedNamedTheory
    {c : ℕ → M} {A : Set (Σ n, Infinitary.Formula namedDeadEndLanguage n)}
    (hs : NamedDeadEndRefutationSupport.{u} A (namedWeaklyRubinTheory c))
    (hAC₀ : InternalChoice V) (hω₀ : HasStandardOmega V)
    (R₀ : BinaryRelationRepresentation (V := V) M) (hM : IsCodedZFModel R₀.code)
    (hcount : IsInternallyCountable R₀.carrier)
    {b₀ : V} (hb₀ : b₀ ∈ R₀.carrier ^ (ω : V))
    (hnames₀ : ∀ n : ℕ, b₀ ‘ (n : V) = (R₀.equiv (c n)).val)
    {H : V} {C : {n : ℕ} → Infinitary.Formula namedDeadEndLanguage n → V}
    (hcode₀ : IsFragmentCoding (namedDeadEndLanguageCode : V) H
      (fun {k} ↦ namedDeadEndFunctionSymbol (V := V) (k := k)) namedDeadEndRelationSymbol C A) : False := by
  obtain ⟨F, hACF, _, N, f, _, _, G, hACG, _, B, E, _, hf, hX⟩ :=
    exists_forced_weaklyRubin_extension hAC₀ hω₀ hM R₀.relation_subset hcount
  obtain ⟨X⟩ := hX
  let J : MembershipEndExtension V G.Model := F.checkEmbedding.trans G.checkEmbedding
  let R₁ := R₀.endExtension J
  have hf' : IsCodedElementaryEmbedding membershipLanguageCode
      (binaryRelationStructureCode R₁.carrier R₁.relation)
      (binaryRelationStructureCode (G.check B) (G.check E)) (G.check f) := hf
  let e₀ : ElementaryMap M (BinaryRelationDomain R₁.carrier R₁.relation) :=
    ⟨R₁.equiv, fun φ b a ↦ R₁.eval_iff φ b a⟩
  let e₁ := hf'.binaryElementaryMap.comp e₀
  have hb₁ : J b₀ ∈ R₁.carrier ^ (ω : G.Model) := by
    change J b₀ ∈ J R₀.carrier ^ (ω : G.Model)
    rw [← J.map_omega]
    exact (J.function_iff b₀ ω R₀.carrier).mpr hb₀
  have hff : G.check f ∈ (G.check B) ^ R₁.carrier := by
    simpa only [binaryRelationStructureCode_domain] using hf'.function
  let t : G.Model := compose (J b₀) (G.check f)
  have ht : t ∈ (G.check B) ^ (ω : G.Model) := compose_function hb₁ hff
  have hnames (n : ℕ) : t ‘ (n : G.Model) = (e₁ (c n)).val := by
    rw [value_compose_of_mem_function hb₁ hff (by simp),
      ← J.map_numeral n, ← J.map_value_total, hnames₀ n]
    rfl
  have hω := standardOmega_of_endExtension J hω₀
  have hcode := namedDeadEndFragmentCoding_endExtension J hcode₀
  have hh := X.holds_namedTheory c e₁ ht hnames hω hcode hs.roots
  apply hs.false_of_endExtension_realization J hω₀ hACG hcode₀ X.carrier_nonempty ht
  simpa only [map_namedDeadEndLanguageCode J] using hh

end ZFVP.Schmerl

