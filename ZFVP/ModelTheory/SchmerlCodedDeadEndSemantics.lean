import ZFVP.ModelTheory.SchmerlCodedDeadEndExpansion
import ZFVP.ModelTheory.SchmerlCodedClassSemantics

/-! The uniform expansion preserves the carrier values used by internal Q. -/

set_option autoImplicit false

namespace ZFVP.BinaryRelationRepresentation

open LO LO.FirstOrder LO.FirstOrder.SetTheory Schmerl
open ZFVP.Infinitary (Formula)
open ZFVP.Infinitary.Internal

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {W : Type*} [SetStructure W]
variable (R : BinaryRelationRepresentation (V := V) W)

noncomputable def representedFunctionColor {G : V} (hG : G ∈ R.carrier ^ (R.carrier ×ˢ R.carrier))
    (s x : W) : W :=
  R.equiv.symm ⟨G ‘ ⟨(R.equiv s).val, (R.equiv x).val⟩ₖ,
    function_value_mem hG (by simp [(R.equiv s).property, (R.equiv x).property])⟩

theorem representedFunctionColor_val {G : V} (hG : G ∈ R.carrier ^ (R.carrier ×ˢ R.carrier))
    (s x : W) :
    (R.equiv (R.representedFunctionColor hG s x)).val = G ‘ ⟨(R.equiv s).val, (R.equiv x).val⟩ₖ :=
  congrArg (fun z : BinaryRelationDomain R.carrier R.relation ↦ z.val) (R.equiv.apply_symm_apply _)

@[instance_reducible] noncomputable def representedDeadEndExpansion {g G : V}
    (hg : g ∈ R.carrier ^ R.carrier) (hG : G ∈ R.carrier ^ (R.carrier ×ˢ R.carrier))
    (c S : V) : Structure deadEndLanguage W :=
  deadEndExpansion (fun x ↦ (R.equiv x).val ∈ range c) (R.representedColor hg)
    (fun s d ↦ ⟨(R.equiv s).val, (R.equiv d).val⟩ₖ ∈ S) (R.representedFunctionColor hG)

variable {g G : V} (hg : g ∈ R.carrier ^ R.carrier)
  (hG : G ∈ R.carrier ^ (R.carrier ×ˢ R.carrier)) (c S : V)

theorem representedDeadEndExpansion_reduct :
    (R.representedDeadEndExpansion hg hG c S).lMap deadEndSetEmbedding =
      (inferInstance : Structure ℒₛₑₜ W) := rfl

theorem representedDeadEndExpansion_eval {ξ : Type*} {n : ℕ} (φ : Semiformula deadEndLanguage ξ n)
    (a : ξ → W) (b : Fin n → W) :
    φ.EvalAux (R.representedDeadEndExpansion hg hG c S) a b ↔
    φ.EvalAux (deadEndExpansion (fun x : BinaryRelationDomain R.carrier R.relation ↦ x.val ∈ range c)
      (classColorFunction hg) (fun s d ↦ ⟨s.val, d.val⟩ₖ ∈ S) (functionColorFunction hG))
      (R.equiv ∘ a) (R.equiv ∘ b) := by
  let : Structure deadEndLanguage W := R.representedDeadEndExpansion hg hG c S
  let : Structure deadEndLanguage (BinaryRelationDomain R.carrier R.relation) :=
    deadEndExpansion (fun x ↦ x.val ∈ range c) (classColorFunction hg)
      (fun s d ↦ ⟨s.val, d.val⟩ₖ ∈ S) (functionColorFunction hG)
  apply Structure.ElementaryEquiv.eval_iff_of_equiv R.equiv (fun _ ↦ rfl) (fun _ ↦ rfl)
  · intro k r v w hvw
    cases r with
    | inl r =>
      cases r with
      | inl r =>
        cases r
        · change v 0 = v 1 ↔ w 0 = w 1
          rw [← R.equiv.injective.eq_iff, hvw 0, hvw 1]
        · change v 0 ∈ v 1 ↔ w 0 ∈ w 1
          rw [R.mem_iff, hvw 0, hvw 1]
      | inr r =>
        cases r
        · change (R.equiv (v 0)).val ∈ range c ↔ (w 0).val ∈ range c
          rw [hvw 0]
        · change v 0 = R.representedColor hg (v 1) ↔ w 0 = classColorFunction hg (w 1)
          rw [← R.equiv_val_injective.eq_iff, R.representedColor_val, hvw 0, hvw 1]
          exact ⟨fun h ↦ Subtype.ext h, fun h ↦ congrArg Subtype.val h⟩
    | inr r =>
      cases r
      · change ⟨(R.equiv (v 0)).val, (R.equiv (v 1)).val⟩ₖ ∈ S ↔ ⟨(w 0).val, (w 1).val⟩ₖ ∈ S
        rw [hvw 0, hvw 1]
      · change v 1 = R.representedFunctionColor hG (v 0) (v 2) ↔
          w 1 = functionColorFunction hG (w 0) (w 2)
        rw [← R.equiv_val_injective.eq_iff, R.representedFunctionColor_val, hvw 0, hvw 1, hvw 2]
        exact ⟨fun h ↦ Subtype.ext h, fun h ↦ congrArg Subtype.val h⟩
  · intro k f
    cases f with
    | inl f =>
      cases f with
      | inl f => exact Empty.elim f
      | inr f => exact Empty.elim f
    | inr f => exact Empty.elim f

noncomputable def deadEndExpansionEquiv :
    W ≃ CodedDomain (codedDeadEndExpansion R.carrier R.relation (range c) g S G) :=
  R.equiv.trans (codedDeadEndExpansionEquiv R.carrier R.relation (range c) g S G).symm

theorem deadEndExpansionEquiv_val (x : W) :
    (R.deadEndExpansionEquiv (g := g) (G := G) c S x).val = (R.equiv x).val := rfl

theorem deadEndExpansionEquiv_Q (A : Set W) :
    R.representedQ A ↔ InternalQ (codedDeadEndExpansion R.carrier R.relation (range c) g S G)
      (R.deadEndExpansionEquiv (g := g) (G := G) c S '' A) := by
  apply not_congr
  apply exists_congr
  intro B
  apply and_congr_right
  intro _
  constructor
  · intro h x hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact h y hy
  · intro h x hx
    exact h (R.deadEndExpansionEquiv c S x) ⟨x, hx, rfl⟩

theorem codedDeadEndExpansion_evalWithQ {n : ℕ} (φ : Infinitary.Formula deadEndLanguage n) (b : Fin n → W) :
    @Formula.EvalWithQ deadEndLanguage W (R.representedDeadEndExpansion hg hG c S) R.representedQ n φ b ↔
    @Formula.EvalWithQ deadEndLanguage
      (CodedDomain (codedDeadEndExpansion R.carrier R.relation (range c) g S G))
      (codedFoundationStructure (codedDeadEndExpansion_valid R.carrier_nonempty R.relation (range c) g S G)
        (fun {k} ↦ deadEndFunctionSymbol (V := V) (k := k)) deadEndRelationSymbol
        (fun _ f ↦ deadEndFunctionSymbol_valid f))
      (InternalQ (codedDeadEndExpansion R.carrier R.relation (range c) g S G)) n φ
      (R.deadEndExpansionEquiv c S ∘ b) := by
  let : Structure deadEndLanguage W := R.representedDeadEndExpansion hg hG c S
  let : Structure deadEndLanguage
      (CodedDomain (codedDeadEndExpansion R.carrier R.relation (range c) g S G)) :=
    codedFoundationStructure (codedDeadEndExpansion_valid R.carrier_nonempty R.relation (range c) g S G)
      (fun {k} ↦ deadEndFunctionSymbol (V := V) (k := k)) deadEndRelationSymbol
      (fun _ f ↦ deadEndFunctionSymbol_valid f)
  apply Formula.evalWithQ_equiv
  · intro k ψ a
    have h₁ := R.representedDeadEndExpansion_eval hg hG c S ψ (Empty.elim : Empty → W) a
    have h₂ := Schmerl.codedDeadEndExpansion_eval R.carrier_nonempty hg hG ψ
      (Empty.elim : Empty → CodedDomain (codedDeadEndExpansion R.carrier R.relation (range c) g S G))
      (R.deadEndExpansionEquiv c S ∘ a)
    have he : R.equiv ∘ (Empty.elim : Empty → W) = Empty.elim := funext fun x ↦ Empty.elim x
    have he' : (fun x : Empty ↦ codedDeadEndExpansionEquiv R.carrier R.relation (range c) g S G
        (Empty.elim x)) = Empty.elim := funext fun x ↦ Empty.elim x
    have hb : (fun i ↦ codedDeadEndExpansionEquiv R.carrier R.relation (range c) g S G
        ((R.deadEndExpansionEquiv c S ∘ a) i)) = R.equiv ∘ a := rfl
    simp only [he] at h₁
    simp only [he', hb] at h₂
    exact h₁.trans h₂.symm
  · exact R.deadEndExpansionEquiv_Q c S

theorem codedDeadEndExpansion_holds (hω : HasStandardOmega V)
    {H : V} {C : {n : ℕ} → Infinitary.Formula deadEndLanguage n → V}
    {A : Set (Σ n, Infinitary.Formula deadEndLanguage n)}
    (hcode : IsFragmentCoding (deadEndLanguageCode (V := V)) H
      (fun {k} ↦ deadEndFunctionSymbol (V := V) (k := k)) deadEndRelationSymbol C A)
    {φ : Infinitary.Formula deadEndLanguage 0} (hA : ⟨0, φ⟩ ∈ A)
    (h : @Formula.EvalWithQ deadEndLanguage W
      (R.representedDeadEndExpansion hg hG c S) R.representedQ 0 φ ![]) :
    Holds (deadEndLanguageCode (V := V)) H
      (codedDeadEndExpansion R.carrier R.relation (range c) g S G) 0 (C φ) ∅ := by
  have h' := (R.codedDeadEndExpansion_evalWithQ hg hG c S φ ![]).mp h
  have he : R.deadEndExpansionEquiv (g := g) (G := G) c S ∘ (![] : Fin 0 → W) = ![] :=
    funext fun i ↦ i.elim0
  rw [he] at h'
  have hh := (hcode.holds_iff_evalWithQ hω
    (codedDeadEndExpansion_valid R.carrier_nonempty R.relation (range c) g S G)
    (fun _ f ↦ deadEndFunctionSymbol_valid f) (fun _ r ↦ deadEndRelationSymbol_valid r)
    φ hA (![] : Fin 0 → CodedDomain (codedDeadEndExpansion R.carrier R.relation (range c) g S G))).mpr h'
  simpa [standardTuple] using hh

end ZFVP.BinaryRelationRepresentation
