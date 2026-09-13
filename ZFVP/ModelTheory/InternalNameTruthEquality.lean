import ZFVP.ModelTheory.InternalNameTruthSemantics
import ZFVP.Syntax.CanonicalEqualityAxioms

/-! Truth of the finite equality basis supplies the exact equivalence and
congruence laws needed by the internal quotient. -/

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem IsNameTruthTable.equality_laws {D E R T : V} (hT : IsNameTruthTable D E R T)
    (hE : E ⊆ D ×ˢ D) (hR : R ⊆ D ×ˢ D)
    (hbasis : TableHolds T 0 (encodeMembershipFormula equalityBasisSentence) ∅) :
    IsInternalSetoid D E ∧ IsInternalRelationCongruence D E R := by
  let : Structure ℒₛₑₜ (SetDomain D) := internalNameStructure D E R
  have ht := (hT.encode_iff equalityBasisSentence (![] : Fin 0 → SetDomain D)).mp
    (by simpa [standardTuple, zero_def] using hbasis)
  have hh : (∀ x : SetDomain D, ⟨x.val, x.val⟩ₖ ∈ E) ∧
      (∀ x y : SetDomain D, ⟨x.val, y.val⟩ₖ ∈ E → ⟨y.val, x.val⟩ₖ ∈ E) ∧
      (∀ x y z : SetDomain D, ⟨x.val, y.val⟩ₖ ∈ E → ⟨y.val, z.val⟩ₖ ∈ E → ⟨x.val, z.val⟩ₖ ∈ E) ∧
      (∀ x y u v : SetDomain D, ⟨x.val, y.val⟩ₖ ∈ E → ⟨u.val, v.val⟩ₖ ∈ E →
        (⟨x.val, u.val⟩ₖ ∈ R ↔ ⟨y.val, v.val⟩ₖ ∈ R)) := by
    simp [equalityBasisSentence, Semiformula.Evalb, Semiformula.Operator.val,
      Semiformula.Operator.Eq.sentence_eq, Semiformula.Operator.Mem.sentence_eq] at ht
    exact ht
  obtain ⟨hr, hs, ht, hm⟩ := hh
  refine ⟨⟨hE, ?_, ?_, ?_⟩, hR, ?_⟩
  · intro x hx
    exact hr ⟨x, hx⟩
  · intro x hx y hy hxy
    exact hs ⟨x, hx⟩ ⟨y, hy⟩ hxy
  · intro x hx y hy z hz hxy hyz
    exact ht ⟨x, hx⟩ ⟨y, hy⟩ ⟨z, hz⟩ hxy hyz
  · intro x hx y hy x' hx' y' hy' hxx' hyy'
    exact hm ⟨x, hx⟩ ⟨x', hx'⟩ ⟨y, hy⟩ ⟨y', hy'⟩ hxx' hyy'

theorem IsNameTruthTable.quotient_codedZF_of_equality {D E R T : V}
    (hD : IsNonempty D) (hT : IsNameTruthTable D E R T) (hE : E ⊆ D ×ˢ D) (hR : R ⊆ D ×ˢ D)
    (hbasis : TableHolds T 0 (encodeMembershipFormula equalityBasisSentence) ∅)
    (hzf : ∀ φ ∈ (zfClosedAxiomCodes : V), TableHolds T 0 φ ∅) :
    IsCodedZFModel (internalQuotientStructure D E R) := by
  obtain ⟨heq, hcong⟩ := hT.equality_laws hE hR hbasis
  exact nameTruthTable_quotient_codedZF hD heq hcong hT hzf

end ZFVP
