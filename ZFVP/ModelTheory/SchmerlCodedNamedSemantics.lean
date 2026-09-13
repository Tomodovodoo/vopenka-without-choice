import ZFVP.ModelTheory.SchmerlCodedNamedLanguage
import ZFVP.ModelTheory.SchmerlCodedClassSemantics

set_option autoImplicit false
namespace ZFVP.Infinitary.Formula
open LO LO.FirstOrder

theorem evalWithQ_lMap {L K : Language} (η : L →ᵥ K) {M : Type*}
    (S : Structure K M) (Q : Set M → Prop) {n : ℕ} (φ : Formula L n) (b : Fin n → M) :
    @EvalWithQ K M S Q n (φ.lMap η) b ↔ @EvalWithQ L M (S.lMap η) Q n φ b := by
  induction φ with
  | fo φ => exact Semiformula.eval_lMap
  | neg φ ih => exact not_congr (ih b)
  | conj φ ih => exact forall_congr' fun i ↦ ih i b
  | exs φ ih => exact exists_congr fun x ↦ ih (x :> b)
  | q φ ih =>
      have he : {x | @EvalWithQ K M S Q _ (φ.lMap η) (x :> b)} =
          {x | @EvalWithQ L M (S.lMap η) Q _ φ (x :> b)} := Set.ext fun x ↦ ih (x :> b)
      change Q _ ↔ Q _
      rw [he]
end ZFVP.Infinitary.Formula

namespace ZFVP.Schmerl
open LO LO.FirstOrder LO.FirstOrder.SetTheory
open ZFVP.Infinitary ZFVP.Infinitary.Internal
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def codedNamedDomainEquiv (D E A g S G t : V) :
    CodedDomain (codedDeadEndExpansion D E A g S G) ≃
      CodedDomain (codedNamedDeadEndExpansion D E A g S G t) where
  toFun x := ⟨x.val, by simpa using x.property⟩
  invFun x := ⟨x.val, by simpa using x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem codedNamedDomainEquiv_Q (D E A g S G t : V)
    (B : Set (CodedDomain (codedDeadEndExpansion D E A g S G))) :
    InternalQ (codedDeadEndExpansion D E A g S G) B ↔
      InternalQ (codedNamedDeadEndExpansion D E A g S G t) (codedNamedDomainEquiv D E A g S G t '' B) := by
  apply not_congr
  apply exists_congr
  intro X
  apply and_congr_right
  intro _
  constructor
  · intro h x hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact h y hy
  · intro h x hx
    exact h (codedNamedDomainEquiv D E A g S G t x) ⟨x, hx, rfl⟩

theorem codedNamedExpansion_reduct_eval {D E A g S G t : V} (hD : IsNonempty D)
    (ht : t ∈ D ^ (ω : V)) {n : ℕ} (φ : Infinitary.Formula deadEndLanguage n)
    (b : Fin n → CodedDomain (codedDeadEndExpansion D E A g S G)) :
    @Formula.EvalWithQ deadEndLanguage _
      (codedFoundationStructure (codedDeadEndExpansion_valid hD E A g S G)
        (fun {k} ↦ deadEndFunctionSymbol (V := V) (k := k)) deadEndRelationSymbol
        (fun _ f ↦ deadEndFunctionSymbol_valid f))
      (InternalQ (codedDeadEndExpansion D E A g S G)) n φ b ↔
    @Formula.EvalWithQ namedDeadEndLanguage _
      (codedFoundationStructure (codedNamedDeadEndExpansion_valid hD E A g S G ht)
        (fun {k} ↦ namedDeadEndFunctionSymbol (V := V) (k := k)) namedDeadEndRelationSymbol
        (fun _ f ↦ namedDeadEndFunctionSymbol_valid f))
      (InternalQ (codedNamedDeadEndExpansion D E A g S G t)) n
      (φ.lMap namedDeadEndEmbedding) (codedNamedDomainEquiv D E A g S G t ∘ b) := by
  let s₀ := codedFoundationStructure (codedDeadEndExpansion_valid hD E A g S G)
    (fun {k} ↦ deadEndFunctionSymbol (V := V) (k := k)) deadEndRelationSymbol
    (fun _ f ↦ deadEndFunctionSymbol_valid f)
  let s₁ := codedFoundationStructure (codedNamedDeadEndExpansion_valid hD E A g S G ht)
    (fun {k} ↦ namedDeadEndFunctionSymbol (V := V) (k := k)) namedDeadEndRelationSymbol
    (fun _ f ↦ namedDeadEndFunctionSymbol_valid f)
  rw [Formula.evalWithQ_lMap]
  let : Structure deadEndLanguage (CodedDomain (codedDeadEndExpansion D E A g S G)) := s₀
  let : Structure deadEndLanguage (CodedDomain (codedNamedDeadEndExpansion D E A g S G t)) :=
    s₁.lMap namedDeadEndEmbedding
  apply Formula.evalWithQ_equiv
  · intro k ψ a
    apply Structure.ElementaryEquiv.eval_iff_of_equiv (codedNamedDomainEquiv D E A g S G t)
      (fun x ↦ x.elim) (fun _ ↦ rfl)
    · intro k r v w hvw
      have hv : (fun i ↦ (v i).val) = (fun i ↦ (w i).val) :=
        funext fun i ↦ congrArg Subtype.val (hvw i)
      change standardTuple (fun i ↦ (v i).val) ∈
        (structureRelations (codedDeadEndExpansion D E A g S G)) ‘ (deadEndRelationSymbol r) ↔
        standardTuple (fun i ↦ (w i).val) ∈
        (structureRelations (codedNamedDeadEndExpansion D E A g S G t)) ‘ (deadEndRelationSymbol r)
      rw [hv]
      simp only [codedNamedDeadEndExpansion, structureRelations_code]
    · intro k f
      cases f with
      | inl f => cases f with
        | inl f => exact f.elim
        | inr f => exact f.elim
      | inr f => exact f.elim
  · exact codedNamedDomainEquiv_Q D E A g S G t

noncomputable def codedNamedBinaryEquiv (D E A g S G t : V) :
    CodedDomain (codedNamedDeadEndExpansion D E A g S G t) ≃ BinaryRelationDomain D E where
  toFun x := ⟨x.val, by simpa using x.property⟩
  invFun x := ⟨x.val, by simpa using x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable def namedConstantValue {D E t : V} (ht : t ∈ D ^ (ω : V)) (n : ℕ) :
    BinaryRelationDomain D E := ⟨t ‘ (n : V), function_value_mem ht (by simp)⟩

theorem codedNamedExpansion_namedSet_eval {D E A g S G t : V} (hD : IsNonempty D)
    (ht : t ∈ D ^ (ω : V)) {ξ : Type*} {n : ℕ} (σ : Semiformula (LSetC ℕ) ξ n)
    (a : ξ → CodedDomain (codedNamedDeadEndExpansion D E A g S G t))
    (b : Fin n → CodedDomain (codedNamedDeadEndExpansion D E A g S G t)) :
    (σ.lMap namedSetEmbedding).EvalAux
      (codedFoundationStructure (codedNamedDeadEndExpansion_valid hD E A g S G ht)
        (fun {k} ↦ namedDeadEndFunctionSymbol (V := V) (k := k)) namedDeadEndRelationSymbol
        (fun _ f ↦ namedDeadEndFunctionSymbol_valid f)) a b ↔
    σ.EvalAux (setConstStructure (BinaryRelationDomain D E) (namedConstantValue ht))
      (codedNamedBinaryEquiv D E A g S G t ∘ a) (codedNamedBinaryEquiv D E A g S G t ∘ b) := by
  let sn := codedFoundationStructure (codedNamedDeadEndExpansion_valid hD E A g S G ht)
    (fun {k} ↦ namedDeadEndFunctionSymbol (V := V) (k := k)) namedDeadEndRelationSymbol
    (fun _ f ↦ namedDeadEndFunctionSymbol_valid f)
  let : Structure (LSetC ℕ) (CodedDomain (codedNamedDeadEndExpansion D E A g S G t)) :=
    sn.lMap namedSetEmbedding
  let : Structure (LSetC ℕ) (BinaryRelationDomain D E) :=
    setConstStructure (BinaryRelationDomain D E) (namedConstantValue ht)
  change (σ.lMap namedSetEmbedding).Eval (s := sn) b a ↔ σ.Eval
    (s := setConstStructure (BinaryRelationDomain D E) (namedConstantValue ht))
    (codedNamedBinaryEquiv D E A g S G t ∘ b) (codedNamedBinaryEquiv D E A g S G t ∘ a)
  rw [Semiformula.eval_lMap]
  apply Structure.ElementaryEquiv.eval_iff_of_equiv (codedNamedBinaryEquiv D E A g S G t)
    (fun _ ↦ rfl) (fun _ ↦ rfl)
  · intro k r v w hvw
    cases r with
    | inr r => exact r.elim
    | inl r =>
        have hv : ∀ i, (v i).val = (w i).val := fun i ↦ congrArg Subtype.val (hvw i)
        have hvm : ∀ i, (v i).val ∈ D := fun i ↦ by simpa using (v i).property
        change standardTuple (fun i ↦ (v i).val) ∈
          (structureRelations (codedNamedDeadEndExpansion D E A g S G t)) ‘
            (deadEndRelationSymbol (deadEndSetEmbedding.rel r)) ↔ _
        simp only [codedNamedDeadEndExpansion, structureRelations_code]
        rw [codedDeadEndExpansion_relation]
        cases r with
        | eq =>
            have h04 : (0 : V) ≠ 4 := natCast_injective.ne (by decide)
            have h05 : (0 : V) ≠ 5 := natCast_injective.ne (by decide)
            change standardTuple (fun i ↦ (v i).val) ∈ deadEndRelationInterpretation D E A g S G (0 : V) ↔ w 0 = w 1
            simp only [deadEndRelationInterpretation, h04, h05, ite_false, classRelationInterpretation, ite_true]
            rw [standardTuple_mem_equalityRelation _ hvm, hv 0, hv 1]
            exact Subtype.val_injective.eq_iff
        | mem =>
            have h14 : (1 : V) ≠ 4 := natCast_injective.ne (by decide)
            have h15 : (1 : V) ≠ 5 := natCast_injective.ne (by decide)
            have h10 : (1 : V) ≠ 0 := natCast_injective.ne (by decide)
            change standardTuple (fun i ↦ (v i).val) ∈ deadEndRelationInterpretation D E A g S G (1 : V) ↔ w 0 ∈ w 1
            simp only [deadEndRelationInterpretation, h14, h15, ite_false, classRelationInterpretation, h10, ite_true]
            rw [standardTuple_mem_binaryTupleRelation _ hvm, hv 0, hv 1]
            rfl
  · intro k f v w hvw
    cases f with
    | inl f => exact f.elim
    | inr f =>
        cases f with
        | const n =>
            apply Subtype.ext
            change ((structureFunctions (codedNamedDeadEndExpansion D E A g S G t)) ‘ (n : V)) ‘
              (standardTuple (fun i : Fin 0 ↦ (v i).val)) = t ‘ (n : V)
            simp only [codedNamedDeadEndExpansion, structureFunctions_code]
            simp only [namedMembershipFunctions]
            rw [value_definableGraph _ _ _ (by simp)]
            exact value_constantGraph _ _ (standardTuple_mem_function _ (fun i ↦ i.elim0))

end ZFVP.Schmerl







