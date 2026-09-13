import ZFVP.ModelTheory.BinaryRelationStructure
import ZFVP.Syntax.MembershipSatisfaction

/-! Satisfaction for a coded arbitrary binary relation agrees with ordinary
first-order evaluation on its represented carrier. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def codedBinaryRelationEquiv (D E : V) :
    CodedDomain (binaryRelationStructureCode D E) ≃ BinaryRelationDomain D E where
  toFun x := ⟨x.val, by simpa using x.property⟩
  invFun x := ⟨x.val, by simpa using x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem binaryRelationStructure_eval {D E : V} (hD : IsNonempty D) {ξ : Type*} {n : ℕ}
    (φ : Semiformula ℒₛₑₜ ξ n)
    (a : ξ → CodedDomain (binaryRelationStructureCode D E))
    (b : Fin n → CodedDomain (binaryRelationStructureCode D E)) :
    φ.EvalAux (codedFoundationStructure (binaryRelationStructureCode_valid hD E)
      (fun {k} ↦ membershipFunctionSymbol (V := V) (k := k)) membershipSymbol
      (fun k f ↦ membershipFunctionSymbol_valid (k := k) f)) a b ↔
    φ.Eval (fun i ↦ codedBinaryRelationEquiv D E (b i))
      (fun x ↦ codedBinaryRelationEquiv D E (a x)) := by
  let : Structure ℒₛₑₜ (CodedDomain (binaryRelationStructureCode D E)) :=
    codedFoundationStructure (binaryRelationStructureCode_valid hD E)
      (fun {k} ↦ membershipFunctionSymbol (V := V) (k := k)) membershipSymbol
      (fun k f ↦ membershipFunctionSymbol_valid (k := k) f)
  apply Structure.ElementaryEquiv.eval_iff_of_equiv (codedBinaryRelationEquiv D E)
    (fun _ ↦ rfl) (fun _ ↦ rfl)
  · intro k r v w hvw
    cases r
    · change standardTuple (fun i ↦ (v i).val) ∈
        (structureRelations (binaryRelationStructureCode D E)) ‘ (0 : V) ↔ w 0 = w 1
      rw [binaryRelationStructureCode_equality, standardTuple_mem_equalityRelation _
        (fun i ↦ by simpa using (v i).property)]
      have hv : ∀ i, (v i).val = (w i).val := fun i ↦ congrArg Subtype.val (hvw i)
      rw [hv 0, hv 1]
      exact Subtype.val_injective.eq_iff
    · change standardTuple (fun i ↦ (v i).val) ∈
        (structureRelations (binaryRelationStructureCode D E)) ‘ (1 : V) ↔ ⟨(w 0).val, (w 1).val⟩ₖ ∈ E
      rw [binaryRelationStructureCode_relation, standardTuple_mem_binaryTupleRelation _
        (fun i ↦ by simpa using (v i).property)]
      have hv : ∀ i, (v i).val = (w i).val := fun i ↦ congrArg Subtype.val (hvw i)
      rw [hv 0, hv 1]
  · intro k f
    exact Empty.elim f

theorem satisfies_encodeBinaryRelationFormula {D E : V} (hD : IsNonempty D) {n : ℕ}
    (φ : SetTheorySemisentence n) (b : Fin n → BinaryRelationDomain D E) :
    Satisfies membershipLanguageCode ∅ (binaryRelationStructureCode D E) ∅ (n : V)
      (encodeMembershipFormula φ) (standardTuple (fun i ↦ (b i).val)) ↔ φ.Evalb b := by
  let c : Fin n → CodedDomain (binaryRelationStructureCode D E) :=
    fun i ↦ (codedBinaryRelationEquiv D E).symm (b i)
  have he : (fun x : Empty ↦ codedBinaryRelationEquiv D E (Empty.elim x)) = Empty.elim :=
    funext (fun x ↦ Empty.elim x)
  exact (encodeSemiformula_satisfies (V := V) (Λ := ℒₛₑₜ) (ξ := Empty)
    (L := membershipLanguageCode) (M := binaryRelationStructureCode D E) (Γ := ∅) (E := ∅)
    (binaryRelationStructureCode_valid hD E)
    (fun {k} ↦ membershipFunctionSymbol (V := V) (k := k)) membershipSymbol
    (fun k f ↦ membershipFunctionSymbol_valid (k := k) f)
    (fun _ r ↦ membershipSymbol_valid r) Empty.elim (fun x ↦ Empty.elim x)
    Empty.elim (fun x ↦ Empty.elim x) c φ).trans (by
      simpa only [c, Equiv.apply_symm_apply, he] using
        binaryRelationStructure_eval hD φ Empty.elim c)

end ZFVP
