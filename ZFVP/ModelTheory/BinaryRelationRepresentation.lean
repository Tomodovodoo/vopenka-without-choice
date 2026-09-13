import ZFVP.Syntax.BinaryRelationSatisfaction

/-! A presentation of an external set-language structure by an internal carrier
and relation, with preservation of all standard first-order formulas. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable (M : Type*) [SetStructure M]

structure BinaryRelationRepresentation where
  carrier : V
  relation : V
  carrier_nonempty : IsNonempty carrier
  relation_subset : relation ⊆ carrier ×ˢ carrier
  equiv : M ≃ BinaryRelationDomain carrier relation
  mem_iff : ∀ x y : M, x ∈ y ↔ equiv x ∈ equiv y

namespace BinaryRelationRepresentation

variable {M} (R : BinaryRelationRepresentation (V := V) M)

noncomputable def code : V := binaryRelationStructureCode R.carrier R.relation

theorem code_valid : IsStructureCode membershipLanguageCode R.code :=
  binaryRelationStructureCode_valid R.carrier_nonempty R.relation

theorem eval_iff {ξ : Type*} {n : ℕ} (φ : Semiformula ℒₛₑₜ ξ n)
    (b : Fin n → M) (a : ξ → M) :
    φ.Eval b a ↔ φ.Eval (R.equiv ∘ b) (R.equiv ∘ a) := by
  apply Structure.ElementaryEquiv.eval_iff_of_equiv R.equiv (fun _ ↦ rfl) (fun _ ↦ rfl)
  · intro k r v w hvw
    cases r
    · change v 0 = v 1 ↔ w 0 = w 1
      rw [← R.equiv.injective.eq_iff, hvw 0, hvw 1]
    · change v 0 ∈ v 1 ↔ w 0 ∈ w 1
      rw [R.mem_iff, hvw 0, hvw 1]
  · intro k f
    exact Empty.elim f

theorem evalb_iff {n : ℕ} (φ : SetTheorySemisentence n) (b : Fin n → M) :
    φ.Evalb b ↔ φ.Evalb (R.equiv ∘ b) := by
  have he : R.equiv ∘ (Empty.elim : Empty → M) = Empty.elim := funext (fun x ↦ Empty.elim x)
  simpa only [he] using R.eval_iff φ b Empty.elim

/-- Internal satisfaction of the standard formula code recovers the original
external structure's truth, including formulas with arbitrary finite parameters. -/
theorem satisfies_iff {n : ℕ} (φ : SetTheorySemisentence n) (b : Fin n → M) :
    Satisfies membershipLanguageCode ∅ R.code ∅ (n : V)
      (encodeMembershipFormula φ) (standardTuple (fun i ↦ (R.equiv (b i)).val)) ↔ φ.Evalb b :=
  (satisfies_encodeBinaryRelationFormula R.carrier_nonempty φ (R.equiv ∘ b)).trans
    (R.evalb_iff φ b).symm

end BinaryRelationRepresentation

end ZFVP
