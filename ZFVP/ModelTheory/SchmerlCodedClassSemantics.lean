import ZFVP.ModelTheory.SchmerlCodedClassRealization
import ZFVP.ModelTheory.SchmerlCodedInfinitarySemantics

/-! Transfer the realization to the actual internal class-language code.
The equivalence preserves the carrier values used by internal Q. -/

set_option autoImplicit false

namespace ZFVP.Infinitary.Formula

open LO LO.FirstOrder

variable {L : Language} {M N : Type*} [Structure L M] [Structure L N]

theorem evalWithQ_equiv (e : M ≃ N) (Q : Set M → Prop) (Q' : Set N → Prop)
    (hfo : ∀ {n} (φ : Semisentence L n) (b : Fin n → M), φ.Evalb b ↔ φ.Evalb (e ∘ b))
    (hQ : ∀ S, Q S ↔ Q' (e '' S)) {n} (φ : Formula L n) (b : Fin n → M) :
    EvalWithQ Q φ b ↔ EvalWithQ Q' φ (e ∘ b) := by
  have he {n} (x : M) (b : Fin n → M) : e ∘ (x :> b) = e x :> (e ∘ b) := by
    funext i
    cases i using Fin.cases <;> rfl
  induction φ with
  | fo φ => exact hfo φ b
  | neg φ ih => exact not_congr (ih b)
  | conj φ ih => exact forall_congr' fun i ↦ ih i b
  | exs φ ih =>
    change (∃ x, EvalWithQ Q φ (x :> b)) ↔ ∃ y, EvalWithQ Q' φ (y :> (e ∘ b))
    constructor
    · rintro ⟨x, hx⟩
      exact ⟨e x, by simpa only [he] using (ih (x :> b)).mp hx⟩
    · rintro ⟨y, hy⟩
      obtain ⟨x, rfl⟩ := e.surjective y
      exact ⟨x, (ih (x :> b)).mpr (by simpa only [he] using hy)⟩
  | q φ ih =>
    change Q {x | EvalWithQ Q φ (x :> b)} ↔ Q' {y | EvalWithQ Q' φ (y :> (e ∘ b))}
    rw [hQ]
    have hs : e '' {x | EvalWithQ Q φ (x :> b)} = {y | EvalWithQ Q' φ (y :> (e ∘ b))} := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        simpa only [he, Set.mem_ofPred_eq] using (ih (x :> b)).mp hx
      · intro hy
        obtain ⟨x, rfl⟩ := e.surjective y
        exact ⟨x, (ih (x :> b)).mpr (by simpa only [he, Set.mem_ofPred_eq] using hy), rfl⟩
    rw [hs]

end ZFVP.Infinitary.Formula

namespace ZFVP.BinaryRelationRepresentation

open LO LO.FirstOrder LO.FirstOrder.SetTheory Schmerl
open ZFVP.Infinitary (Formula)
open ZFVP.Infinitary.Internal

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {W : Type*} [SetStructure W] [Nonempty W] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable (R : BinaryRelationRepresentation (V := V) W) {g : V} (hg : g ∈ R.carrier ^ R.carrier) (c : V)

omit [Nonempty W] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
theorem representedClassExpansion_eval {ξ : Type*} {n : ℕ} (φ : Semiformula classLanguage ξ n)
    (a : ξ → W) (b : Fin n → W) :
    φ.EvalAux (R.representedClassExpansion hg c) a b ↔
    φ.EvalAux (classExpansion (fun x : BinaryRelationDomain R.carrier R.relation ↦ x.val ∈ range c)
      (classColorFunction hg)) (R.equiv ∘ a) (R.equiv ∘ b) := by
  let : Structure classLanguage W := R.representedClassExpansion hg c
  let : Structure classLanguage (BinaryRelationDomain R.carrier R.relation) :=
    classExpansion (fun x ↦ x.val ∈ range c) (classColorFunction hg)
  apply Structure.ElementaryEquiv.eval_iff_of_equiv R.equiv (fun _ ↦ rfl) (fun _ ↦ rfl)
  · intro k r v w hvw
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
        exact ⟨fun h ↦ Subtype.ext h, fun h ↦ congrArg (fun x : BinaryRelationDomain R.carrier R.relation ↦ x.val) h⟩
  · intro k f
    cases f with
    | inl f => exact Empty.elim f
    | inr f => exact Empty.elim f

noncomputable def classExpansionEquiv : W ≃ CodedDomain (codedClassExpansion R.carrier R.relation (range c) g) :=
  R.equiv.trans (codedClassExpansionEquiv R.carrier R.relation (range c) g).symm

omit [Nonempty W] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
theorem classExpansionEquiv_val (x : W) :
    (R.classExpansionEquiv (g := g) c x).val = (R.equiv x).val := rfl

omit [Nonempty W] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
theorem classExpansionEquiv_Q (S : Set W) :
    R.representedQ S ↔ InternalQ (codedClassExpansion R.carrier R.relation (range c) g)
      (R.classExpansionEquiv (g := g) c '' S) := by
  apply not_congr
  apply exists_congr
  intro A
  apply and_congr_right
  intro _
  constructor
  · intro h x hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact h y hy
  · intro h x hx
    exact h (R.classExpansionEquiv c x) ⟨x, hx, rfl⟩

omit [Nonempty W] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
theorem codedClassExpansion_evalWithQ {n : ℕ} (φ : Formula classLanguage n) (b : Fin n → W) :
    @Formula.EvalWithQ classLanguage W (R.representedClassExpansion hg c) R.representedQ n φ b ↔
    @Formula.EvalWithQ classLanguage (CodedDomain (codedClassExpansion R.carrier R.relation (range c) g))
      (codedFoundationStructure (codedClassExpansion_valid R.carrier_nonempty R.relation (range c) g)
        (fun {k} ↦ classFunctionSymbol (V := V) (k := k)) classRelationSymbol
        (fun _ f ↦ classFunctionSymbol_valid f))
      (InternalQ (codedClassExpansion R.carrier R.relation (range c) g)) n φ
      (R.classExpansionEquiv c ∘ b) := by
  let : Structure classLanguage W := R.representedClassExpansion hg c
  let : Structure classLanguage (CodedDomain (codedClassExpansion R.carrier R.relation (range c) g)) :=
    codedFoundationStructure (codedClassExpansion_valid R.carrier_nonempty R.relation (range c) g)
      (fun {k} ↦ classFunctionSymbol (V := V) (k := k)) classRelationSymbol
      (fun _ f ↦ classFunctionSymbol_valid f)
  apply Formula.evalWithQ_equiv
  · intro k ψ a
    have h₁ := R.representedClassExpansion_eval hg c ψ (Empty.elim : Empty → W) a
    have h₂ := Schmerl.codedClassExpansion_eval R.carrier_nonempty hg ψ
      (Empty.elim : Empty → CodedDomain (codedClassExpansion R.carrier R.relation (range c) g))
      (R.classExpansionEquiv c ∘ a)
    have he : R.equiv ∘ (Empty.elim : Empty → W) = Empty.elim := funext fun x ↦ Empty.elim x
    have he' : (fun x : Empty ↦ codedClassExpansionEquiv R.carrier R.relation (range c) g (Empty.elim x)) =
        Empty.elim := funext fun x ↦ Empty.elim x
    have hb : (fun i ↦ codedClassExpansionEquiv R.carrier R.relation (range c) g
        ((R.classExpansionEquiv c ∘ a) i)) = R.equiv ∘ a := rfl
    simp only [he] at h₁
    simp only [he', hb] at h₂
    exact h₁.trans h₂.symm
  · exact R.classExpansionEquiv_Q c

omit [Nonempty W] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
theorem codedClassExpansion_holds (hω : HasStandardOmega V)
    {H : V} {C : {n : ℕ} → Infinitary.Formula classLanguage n → V}
    {A : Set (Σ n, Infinitary.Formula classLanguage n)}
    (hcode : IsFragmentCoding (classLanguageCode (V := V)) H
      (fun {k} ↦ classFunctionSymbol (V := V) (k := k)) classRelationSymbol C A)
    (hA : ⟨0, classTreeSentence⟩ ∈ A)
    (h : @Formula.EvalWithQ classLanguage W (R.representedClassExpansion hg c) R.representedQ 0 classTreeSentence ![]) :
    Holds (classLanguageCode (V := V)) H (codedClassExpansion R.carrier R.relation (range c) g)
      0 (C classTreeSentence) ∅ := by
  have h' := (R.codedClassExpansion_evalWithQ hg c classTreeSentence ![]).mp h
  have he : R.classExpansionEquiv (g := g) c ∘ (![] : Fin 0 → W) = ![] := funext fun i ↦ i.elim0
  rw [he] at h'
  have hh := (hcode.holds_iff_evalWithQ hω (codedClassExpansion_valid R.carrier_nonempty R.relation (range c) g)
    (fun _ f ↦ classFunctionSymbol_valid f) (fun _ r ↦ classRelationSymbol_valid r)
    classTreeSentence hA (![] : Fin 0 → CodedDomain (codedClassExpansion R.carrier R.relation (range c) g))).mpr h'
  simpa [standardTuple] using hh

end ZFVP.BinaryRelationRepresentation
