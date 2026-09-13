import ZFVP.ModelTheory.InternalBinaryQuotient

/-! Formula truth descends from names to the actual internal quotient.
Equality on names is the internal equivalence relation. -/
namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

@[instance_reducible] noncomputable def internalNameStructure (D E R : V) : Structure ℒₛₑₜ (SetDomain D) where
  func _ f := nomatch f
  rel _ r v := match r with
    | .eq => ⟨(v 0).val, (v 1).val⟩ₖ ∈ E
    | .mem => ⟨(v 0).val, (v 1).val⟩ₖ ∈ R

noncomputable def internalQuotientMap (D E R : V) (x : SetDomain D) :
    BinaryRelationDomain (internalQuotientCarrier D E) (internalQuotientEdges D E R) :=
  ⟨internalEquivalenceClass D E x.val, (mem_internalQuotientCarrier _ _ _).mpr ⟨x.val, x.property, rfl⟩⟩

theorem internalQuotientMap_surjective (D E R : V) : Function.Surjective (internalQuotientMap D E R) := by
  rintro ⟨q, hq⟩
  obtain ⟨x, hx, rfl⟩ := (mem_internalQuotientCarrier _ _ _).mp hq
  exact ⟨⟨x, hx⟩, rfl⟩

theorem IsInternalSetoid.quotientMap_relation_iff {D E R : V} (h : IsInternalSetoid D E)
    (hR : IsInternalRelationCongruence D E R) {k} (r : Language.Set.Rel k) (v : Fin k → SetDomain D) :
    (internalNameStructure D E R).rel r v ↔
      Structure.rel (L := ℒₛₑₜ) r (internalQuotientMap D E R ∘ v) := by
  cases r with
  | eq =>
    change ⟨(v 0).val, (v 1).val⟩ₖ ∈ E ↔ internalQuotientMap D E R (v 0) = internalQuotientMap D E R (v 1)
    constructor
    · intro he
      exact Subtype.ext ((h.classes_eq_iff (v 0).property (v 1).property).mpr he)
    · intro he
      exact (h.classes_eq_iff (v 0).property (v 1).property).mp
        (congrArg (fun z : BinaryRelationDomain (internalQuotientCarrier D E) (internalQuotientEdges D E R) ↦ z.val) he)
  | mem =>
    exact (h.quotient_edge_iff hR (v 0).property (v 1).property).symm

variable {D E R : V}

private theorem quotientMap_term {ξ : Type*} {n} (b : Fin n → SetDomain D) (f : ξ → SetDomain D)
    (t : Semiterm ℒₛₑₜ ξ n) :
    internalQuotientMap D E R (t.val (s := internalNameStructure D E R) b f) =
      t.val (internalQuotientMap D E R ∘ b) (internalQuotientMap D E R ∘ f) := by
  cases t with
  | bvar i => rfl
  | fvar x => rfl
  | func g _ => cases g

theorem IsInternalSetoid.quotientMap_eval_iff (h : IsInternalSetoid D E)
    (hR : IsInternalRelationCongruence D E R) {ξ : Type*} {n}
    (φ : SetTheorySemiformula ξ n) (b : Fin n → SetDomain D) (f : ξ → SetDomain D) :
    φ.Eval (s := internalNameStructure D E R) b f ↔
      φ.Eval (internalQuotientMap D E R ∘ b) (internalQuotientMap D E R ∘ f) := by
  let := internalNameStructure D E R
  have ht {n k} (b : Fin n → SetDomain D) (ts : Fin k → Semiterm ℒₛₑₜ ξ n) :
      (fun i ↦ (ts i).val (internalQuotientMap D E R ∘ b) (internalQuotientMap D E R ∘ f)) =
        internalQuotientMap D E R ∘ (fun i ↦ (ts i).val b f) := by
    funext i
    exact (quotientMap_term b f (ts i)).symm
  revert b
  induction φ using Semiformula.rec' with
  | hverum => intro b; rfl
  | hfalsum => intro b; rfl
  | hrel r ts =>
    intro b
    simp only [Semiformula.eval_rel', ht]
    exact h.quotientMap_relation_iff hR r _
  | hnrel r ts =>
    intro b
    simp only [Semiformula.eval_nrel', ht]
    exact not_congr (h.quotientMap_relation_iff hR r _)
  | hand φ ψ ihφ ihψ => intro b; exact and_congr (ihφ b) (ihψ b)
  | hor φ ψ ihφ ihψ => intro b; exact or_congr (ihφ b) (ihψ b)
  | hall φ ih =>
    intro b
    simp only [Semiformula.eval_all]
    constructor
    · intro hh y
      obtain ⟨x, rfl⟩ := internalQuotientMap_surjective D E R y
      simpa only [Function.comp_def, Matrix.comp_vecCons'] using (ih (x :> b)).mp (hh x)
    · intro hh x
      apply (ih (x :> b)).mpr
      simpa only [Function.comp_def, Matrix.comp_vecCons'] using hh (internalQuotientMap D E R x)
  | hexs φ ih =>
    intro b
    simp only [Semiformula.eval_ex]
    constructor
    · rintro ⟨x, hh⟩
      refine ⟨internalQuotientMap D E R x, ?_⟩
      simpa only [Function.comp_def, Matrix.comp_vecCons'] using (ih (x :> b)).mp hh
    · rintro ⟨y, hh⟩
      obtain ⟨x, rfl⟩ := internalQuotientMap_surjective D E R y
      refine ⟨x, (ih (x :> b)).mpr ?_⟩
      simpa only [Function.comp_def, Matrix.comp_vecCons'] using hh

end ZFVP



