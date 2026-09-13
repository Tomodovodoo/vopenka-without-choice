import ZFVP.ModelTheory.SchmerlCodedCountableUpperBound
import ZFVP.ModelTheory.InternalNamedSeparationOmission

/-! An internal common upper bound gives an actual coded separator. -/

set_option autoImplicit false

namespace ZFVP.Schmerl

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def upperInitialSegment (P R e : V) : V := {x ∈ P ; ⟨x, e⟩ₖ ∈ R}

theorem mem_upperInitialSegment {P R e x : V} :
    x ∈ upperInitialSegment P R e ↔ x ∈ P ∧ ⟨x, e⟩ₖ ∈ R := mem_sep_iff

/-- The binary definition becomes a unary definition by prepending `e` to its parameters. -/
theorem isCodedDefinableSet_upperInitialSegment {N P R e : V}
    (hP : P ⊆ structureDomain N) (hR : R ⊆ P ×ˢ P)
    (hdef : IsCodedDefinableRelation N R) (he : e ∈ structureDomain N) :
    IsCodedDefinableSet N (upperInitialSegment P R e) := by
  obtain ⟨_, n, hn, φ, hφ, b, hb, hφb⟩ := hdef
  refine ⟨fun x hx ↦ hP x (mem_upperInitialSegment.mp hx).1,
    succ n, ω_succ_closed hn, φ, hφ, assignmentPrepend n b e,
    assignmentPrepend_mem_function hn hb he, fun x hx ↦ ?_⟩
  rw [mem_upperInitialSegment]
  constructor
  · exact fun h ↦ (hφb x hx e he).mp h.2
  · intro h
    have hxe := (hφb x hx e he).mpr h
    exact ⟨(kpair_mem_iff.mp (hR _ hxe)).1, hxe⟩

theorem upperInitialSegment_separates {P R U W e : V} (he : e ∈ P)
    (hUP : U ⊆ P) (hue : ∀ u ∈ U, ⟨u, e⟩ₖ ∈ R)
    (hW : ∀ q ∈ W, q ∈ P → ∃ u ∈ U,
      ¬∃ z ∈ P, ⟨u, z⟩ₖ ∈ R ∧ ⟨q, z⟩ₖ ∈ R) :
    U ⊆ upperInitialSegment P R e ∧ ∀ q ∈ W, q ∉ upperInitialSegment P R e := by
  refine ⟨fun u hu ↦ mem_upperInitialSegment.mpr ⟨hUP u hu, hue u hu⟩,
    fun q hq hqe ↦ ?_⟩
  obtain ⟨hqP, hqe⟩ := mem_upperInitialSegment.mp hqe
  obtain ⟨u, hu, hincomp⟩ := hW q hq hqP
  exact hincomp ⟨e, he, hue u hu, hqe⟩

/-- The regular-cardinal form isolates precisely the hypotheses needed for separation. -/
theorem exists_codedSeparator_of_countable_cofinalChain {κ N P R F c U W : V}
    (hκ : IsRegularCardinal κ) (hω : (ω : V) ∈ κ)
    (hP : P ⊆ structureDomain N) (hdef : IsCodedDefinableRelation N R)
    (hR : IsForcingPreorder P R) (hFP : F ⊆ P)
    (hc : IsInternalCofinalStrictChain κ F R c)
    (hU : IsInternallyCountable U) (hUF : U ⊆ F)
    (hW : ∀ q ∈ W, q ∈ P → ∃ u ∈ U,
      ¬∃ z ∈ P, ⟨u, z⟩ₖ ∈ R ∧ ⟨q, z⟩ₖ ∈ R) :
    ∃ X, IsCodedDefinableSet N X ∧ U ⊆ X ∧ ∀ q ∈ W, q ∉ X := by
  obtain ⟨e, he, hue⟩ := exists_countable_cofinalChain_upperBound hκ hω hR hFP hc hU hUF
  exact ⟨upperInitialSegment P R e,
    isCodedDefinableSet_upperInitialSegment hP hR.1 hdef (hP e (hFP e he)),
    upperInitialSegment_separates (hFP e he) (fun u hu ↦ hFP u (hUF u hu)) hue hW⟩

/-- The final Rubin obstruction, with every formula, parameter tuple, and countable set internal. -/
theorem not_codedInseparable_of_countable_cofinalChain (hAC : InternalChoice V)
    {N P R F c U W : V} (hP : IsCodedDefinableSet N P)
    (hdef : IsCodedDefinableRelation N R) (hR : IsForcingPoset P R)
    (hF : IsInternalMaximallyCompatible P R F)
    (hc : IsInternalCofinalStrictChain (hartogsNumber (ω : V)) F R c)
    (hU : IsInternallyCountable U) (hUF : U ⊆ F)
    (hW : ∀ q ∈ W, q ∈ P → ∃ u ∈ U,
      ¬∃ z ∈ P, ⟨u, z⟩ₖ ∈ R ∧ ⟨q, z⟩ₖ ∈ R) :
    ¬IsCodedInseparable N U W := by
  intro hsep
  exact hsep.2.2 (exists_codedSeparator_of_countable_cofinalChain
    (hartogsNumber_regular hAC (CardLE.refl _)) omega_mem_hartogs_omega
    hP.1 hdef hR.1 hF.1 hc hU hUF hW)

end ZFVP.Schmerl
