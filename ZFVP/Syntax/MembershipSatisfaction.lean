import ZFVP.ModelTheory.MembershipStructure
import ZFVP.SetTheory.BoundedFormulas

/-! Set-coded satisfaction agrees with evaluation on the represented set. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def membershipFunctionSymbol {k : ℕ} (f : Language.Set.Func k) : V := Empty.elim f

theorem membershipFunctionSymbol_valid {k : ℕ} (f : Language.Set.Func k) :
    membershipFunctionSymbol f ∈ functionSymbols (membershipLanguageCode : V) ∧
      (functionArities (membershipLanguageCode : V)) ‘ (membershipFunctionSymbol f) = (k : V) :=
  Empty.elim f

def codedMembershipEquiv (A : V) : CodedDomain (membershipStructureCode A) ≃ SetDomain A where
  toFun x := ⟨x.val, by simpa using x.property⟩
  invFun x := ⟨x.val, by simpa using x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem membershipStructure_eval {A : V} (hA : IsNonempty A) {n : ℕ}
    (φ : SetTheorySemisentence n) (b : Fin n → CodedDomain (membershipStructureCode A)) :
    φ.EvalAux (codedFoundationStructure (membershipStructureCode_valid hA)
      (fun {k} ↦ membershipFunctionSymbol (V := V) (k := k)) membershipSymbol (fun k f ↦ membershipFunctionSymbol_valid (k := k) f)) Empty.elim b ↔
    φ.Evalb (fun i ↦ codedMembershipEquiv A (b i)) := by
  let : Structure ℒₛₑₜ (CodedDomain (membershipStructureCode A)) :=
    codedFoundationStructure (membershipStructureCode_valid hA)
      (fun {k} ↦ membershipFunctionSymbol (V := V) (k := k)) membershipSymbol
      (fun k f ↦ membershipFunctionSymbol_valid (k := k) f)
  apply Structure.ElementaryEquiv.eval_iff_of_equiv (codedMembershipEquiv A) (fun x ↦ Empty.elim x) (fun _ ↦ rfl)
  · intro k r v w hvw
    cases r
    · change standardTuple (fun i ↦ (v i).val) ∈
        (structureRelations (membershipStructureCode A)) ‘ (0 : V) ↔ w 0 = w 1
      rw [membershipStructureCode_equality, standardTuple_mem_equalityRelation _
        (fun i ↦ by simpa using (v i).property)]
      have hv : ∀ i, (v i).val = (w i).val := fun i ↦ congrArg Subtype.val (hvw i)
      rw [hv 0, hv 1]
      exact Subtype.val_injective.eq_iff
    · change standardTuple (fun i ↦ (v i).val) ∈
        (structureRelations (membershipStructureCode A)) ‘ (1 : V) ↔ (w 0).val ∈ (w 1).val
      rw [membershipStructureCode_membership, standardTuple_mem_membershipTupleRelation _
        (fun i ↦ by simpa using (v i).property)]
      have hv : ∀ i, (v i).val = (w i).val := fun i ↦ congrArg Subtype.val (hvw i)
      rw [hv 0, hv 1]
  · intro k f
    exact Empty.elim f

noncomputable def encodeMembershipFormula {n : ℕ} (φ : SetTheorySemisentence n) : V :=
  encodeSemiformula (fun {k} ↦ membershipFunctionSymbol (V := V) (k := k)) membershipSymbol Empty.elim φ

theorem encodeMembershipFormula_mem {n : ℕ} (φ : SetTheorySemisentence n) :
    encodeMembershipFormula φ ∈ formulaSet (membershipLanguageCode : V) ∅ (n : V) := by
  refine (mem_formulaSet_iff (membershipLanguageCode : V) ∅ (n : V) (encodeMembershipFormula φ)).mpr ?_
  exact encodeSemiformula_mem_family (V := V) (Λ := ℒₛₑₜ) (ξ := Empty)
    (L := membershipLanguageCode) (Γ := ∅) membershipLanguageCode_valid
    (fun {k} ↦ membershipFunctionSymbol (V := V) (k := k)) membershipSymbol Empty.elim
    (fun k f ↦ membershipFunctionSymbol_valid (k := k) f) (fun _ r ↦ membershipSymbol_valid r)
    (fun x ↦ Empty.elim x) φ

theorem satisfies_encodeMembershipFormula {A : V} (hA : IsNonempty A) {n : ℕ}
    (φ : SetTheorySemisentence n) (b : Fin n → SetDomain A) :
    Satisfies membershipLanguageCode ∅ (membershipStructureCode A) ∅ (n : V)
      (encodeMembershipFormula φ) (standardTuple (fun i ↦ (b i).val)) ↔ φ.Evalb b := by
  let c : Fin n → CodedDomain (membershipStructureCode A) := fun i ↦ (codedMembershipEquiv A).symm (b i)
  exact (encodeSemiformula_satisfies (V := V) (Λ := ℒₛₑₜ) (ξ := Empty)
    (L := membershipLanguageCode) (M := membershipStructureCode A) (Γ := ∅) (E := ∅)
    (membershipStructureCode_valid hA)
    (fun {k} ↦ membershipFunctionSymbol (V := V) (k := k)) membershipSymbol (fun k f ↦ membershipFunctionSymbol_valid (k := k) f)
    (fun _ r ↦ membershipSymbol_valid r) Empty.elim (fun x ↦ Empty.elim x)
    Empty.elim (fun x ↦ Empty.elim x) c φ).trans (membershipStructure_eval hA φ c)

theorem satisfies_boundedMembershipFormula {A : V} (hA : IsNonempty A) [IsTransitive A]
    {n : ℕ} {φ : SetTheorySemisentence n} (hφ : IsBoundedSetFormula φ) (b : Fin n → SetDomain A) :
    Satisfies membershipLanguageCode ∅ (membershipStructureCode A) ∅ (n : V)
      (encodeMembershipFormula φ) (standardTuple (fun i ↦ (b i).val)) ↔
      φ.Evalb (fun i ↦ (b i).val) :=
  (satisfies_encodeMembershipFormula hA φ b).trans (bounded_formula_absolute A hφ b)

end ZFVP





