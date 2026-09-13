import ZFVP.ModelTheory.SeparatingTypesOmitted
import ZFVP.ModelTheory.StageCarrier
import ZFVP.SetTheory.MembershipIso

/-! # The successor step of Enayat's ω₁-length construction

Enayat's Appendix (Stage 1 of Theorem A.1) builds an increasing ω₁-chain of countable models,
all of them living on subsets of one fixed set of size `ℵ₁`; conditions (1) to (3) at stage
`α + 1` ask for a countable elementary extension of the previous stage that keeps the inseparable
pairs inseparable and bounds each definable directed set, placed on a countable superset of the
previous carrier.

Lemma A.2 (`ZFVP.exists_elementary_extension_inseparable_upper_bounds'`) produces the extension as
an abstract type. This file moves it onto the fixed carrier, using
`ZFVP.exists_carrier_extension`. No model theory is proved here: everything is Lemma A.2 plus
transport along a bijection.

* `StageModel Ω` is a subset of the carrier `Ω` with a membership relation on it, and
  `IsStageExtension` is the order between stages: inclusion of carriers together with agreement of
  the two membership relations on the smaller one.
* `StageModel.ofEquiv` puts a model `N` on a subset `B` of the carrier along a bijection
  `↥B ≃ N`, and `StageModel.ofEquivMap` is that bijection read as an elementary map.
* `exists_stage_successor` is the step: the extension of Lemma A.2, placed on a countable superset
  of the current carrier, with the old points not moved.

The membership relation of a `StageModel` is written in the reading `mem x y` for "`x` is an
element of `y`", so the `SetStructure` instance flips the arguments: Lean's `Membership.mem`
takes the container first.
-/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

universe u v

/-! ## Stages -/

/-- A stage of the construction: a subset of the fixed carrier `Ω` together with a membership
relation on it. `mem x y` reads "`x` is an element of `y`". -/
structure StageModel (Ω : Type u) where
  /-- The set of points of the carrier used by this stage. -/
  carrier : Set Ω
  /-- The membership relation of the stage; `mem x y` says that `x` is an element of `y`. -/
  mem : ↥carrier → ↥carrier → Prop

/-- A stage is a structure for the membership language. `Membership.mem` takes the container
first, so the arguments of `StageModel.mem` are flipped here. -/
instance stageSetStructure {Ω : Type u} (S : StageModel Ω) : SetStructure ↥S.carrier :=
  ⟨fun y x ↦ S.mem x y⟩

@[simp] theorem stageModel_mem_iff {Ω : Type u} (S : StageModel Ω) (x y : ↥S.carrier) :
    x ∈ y ↔ S.mem x y := Iff.rfl

/-- The inclusion of the points of one stage into a larger one. -/
def StageModel.incl {Ω : Type u} {S T : StageModel Ω} (h : S.carrier ⊆ T.carrier) :
    ↥S.carrier → ↥T.carrier := Set.inclusion h

theorem StageModel.incl_injective {Ω : Type u} {S T : StageModel Ω} (h : S.carrier ⊆ T.carrier) :
    Function.Injective (StageModel.incl h) := Set.inclusion_injective h

@[simp] theorem StageModel.coe_incl {Ω : Type u} {S T : StageModel Ω} (h : S.carrier ⊆ T.carrier)
    (x : ↥S.carrier) : ((StageModel.incl h x : ↥T.carrier) : Ω) = (x : Ω) := rfl

theorem StageModel.coe_comp_incl {Ω : Type u} {S T : StageModel Ω} (h : S.carrier ⊆ T.carrier) :
    (fun x : ↥T.carrier ↦ (x : Ω)) ∘ StageModel.incl h = fun x : ↥S.carrier ↦ (x : Ω) := rfl

/-- One stage extends another if its carrier is larger and the two membership relations agree on
the smaller carrier. Elementarity of the inclusion is not part of this; it is carried separately,
as a bundled elementary map, where it is needed. -/
def IsStageExtension {Ω : Type u} (S T : StageModel Ω) : Prop :=
  ∃ h : S.carrier ⊆ T.carrier,
    ∀ x y : ↥S.carrier, S.mem x y ↔ T.mem (StageModel.incl h x) (StageModel.incl h y)

theorem isStageExtension_refl {Ω : Type u} (S : StageModel Ω) : IsStageExtension S S :=
  ⟨subset_rfl, fun _ _ ↦ Iff.rfl⟩

/-! ## Putting a model on a subset of the carrier -/

section OfEquiv

variable {Ω : Type u} {N : Type v} [SetStructure N]

/-- The stage on `B` obtained by pulling the membership relation of `N` back along a bijection
`e : ↥B ≃ N`. -/
def StageModel.ofEquiv (B : Set Ω) (e : ↥B ≃ N) : StageModel Ω where
  carrier := B
  mem x y := e x ∈ e y

@[simp] theorem StageModel.ofEquiv_carrier (B : Set Ω) (e : ↥B ≃ N) :
    (StageModel.ofEquiv B e).carrier = B := rfl

/-- The same bijection, with its domain written as the carrier of the stage. The two types are the
same by definition; the second spelling is the one that makes the membership relation of the stage
visible to typeclass search. -/
def StageModel.ofEquivEquiv (B : Set Ω) (e : ↥B ≃ N) :
    ↥(StageModel.ofEquiv B e).carrier ≃ N := e

@[simp] theorem StageModel.ofEquivEquiv_apply (B : Set Ω) (e : ↥B ≃ N)
    (x : ↥(StageModel.ofEquiv B e).carrier) : StageModel.ofEquivEquiv B e x = e x := rfl

theorem StageModel.ofEquiv_mem_iff (B : Set Ω) (e : ↥B ≃ N)
    (x y : ↥(StageModel.ofEquiv B e).carrier) :
    x ∈ y ↔ StageModel.ofEquivEquiv B e x ∈ StageModel.ofEquivEquiv B e y := Iff.rfl

/-- The bijection placing `N` on `B` is an elementary map: it is an isomorphism of membership
structures by construction. -/
def StageModel.ofEquivMap (B : Set Ω) (e : ↥B ≃ N) :
    ElementaryMap ↥(StageModel.ofEquiv B e).carrier N :=
  ElementaryMap.ofMembershipIso (StageModel.ofEquivEquiv B e) fun _ _ ↦ Iff.rfl

@[simp] theorem StageModel.ofEquivMap_apply (B : Set Ω) (e : ↥B ≃ N)
    (x : ↥(StageModel.ofEquiv B e).carrier) : StageModel.ofEquivMap B e x = e x := rfl

/-- The inverse bijection is an elementary map back onto the stage. -/
def StageModel.ofEquivSymmMap (B : Set Ω) (e : ↥B ≃ N) :
    ElementaryMap N ↥(StageModel.ofEquiv B e).carrier :=
  ElementaryMap.ofMembershipIso (StageModel.ofEquivEquiv B e).symm fun x y ↦ by
    rw [StageModel.ofEquiv_mem_iff, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

@[simp] theorem StageModel.ofEquivSymmMap_apply (B : Set Ω) (e : ↥B ≃ N) (x : N) :
    StageModel.ofEquivSymmMap B e x = (StageModel.ofEquivEquiv B e).symm x := rfl

end OfEquiv

/-! ## Transporting definability and inseparability along a membership isomorphism -/

section Transport

variable {A B : Type*} [SetStructure A] [SetStructure B]

/-- A definable predicate stays definable when pulled back along a membership isomorphism: rewrite
the parameters of the defining formula along the inverse bijection. -/
theorem definable_comp_memEquiv (e : A ≃ B) (he : ∀ x y, e x ∈ e y ↔ x ∈ y) {X : B → Prop}
    (hX : ℒₛₑₜ-predicate[B] X) : ℒₛₑₜ-predicate[A] fun x ↦ X (e x) := by
  obtain ⟨φ, hφ⟩ := hX.definable
  refine ⟨Rew.rewriteMap (fun y : B ↦ e.symm y) ▹ φ, fun v ↦ ?_⟩
  rw [Semiformula.eval_rewriteMap]
  have h := eval_membershipIso e he φ v (fun y : B ↦ e.symm y)
  have hcomp : (⇑e ∘ fun y : B ↦ e.symm y) = id := funext fun y ↦ e.apply_symm_apply y
  rw [hcomp] at h
  simp only [id_eq]
  rw [h]
  exact hφ (fun i ↦ e (v i))

/-- Inseparability is preserved by pointwise equivalent descriptions of the two sets. -/
theorem Inseparable.congr {V W V' W' : B → Prop} (h : Inseparable B V W)
    (hV : ∀ x, V' x ↔ V x) (hW : ∀ x, W' x ↔ W x) : Inseparable B V' W' := by
  rintro ⟨X, hX, hVX, hWX⟩
  exact h ⟨X, hX, fun x hx ↦ hVX x ((hV x).mpr hx), fun x hx ↦ hWX x ((hW x).mpr hx)⟩

/-- Inseparability transports along a membership isomorphism. -/
theorem Inseparable.comp_memEquiv (e : A ≃ B) (he : ∀ x y, e x ∈ e y ↔ x ∈ y) {V W : B → Prop}
    (h : Inseparable B V W) : Inseparable A (fun x ↦ V (e x)) fun x ↦ W (e x) := by
  have hsymm : ∀ x y : B, e.symm x ∈ e.symm y ↔ x ∈ y := by
    intro x y
    rw [← he (e.symm x) (e.symm y), Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  rintro ⟨X, hX, hVX, hWX⟩
  refine h ⟨fun y ↦ X (e.symm y), definable_comp_memEquiv e.symm hsymm hX, fun y hy ↦ ?_,
    fun y hy ↦ ?_⟩
  · exact hVX (e.symm y) (by simpa using hy)
  · exact hWX (e.symm y) (by simpa using hy)

end Transport

/-! ## Small helpers for composing with tuples -/

section Tuples

variable {A B : Type*}

theorem comp_vec_one (g : A → B) (x : A) : g ∘ ![x] = ![g x] := by
  funext i
  refine Fin.cases rfl (fun j ↦ ?_) i
  exact j.elim0

theorem comp_vec_two (g : A → B) (x y : A) : g ∘ ![x, y] = ![g x, g y] := by
  funext i
  refine Fin.cases rfl (fun j ↦ ?_) i
  refine Fin.cases rfl (fun l ↦ ?_) j
  exact l.elim0

end Tuples

/-! ## The successor step -/

/-- The successor step of Enayat's construction. Given a countable stage `S` on a carrier of size
`ℵ₁`, countably many inseparable pairs and countably many definable directed sets with no last
element, there is a countable stage `T` on a larger subset of the same carrier such that the
inclusion of `S` into `T` is elementary, the pairs stay inseparable and each directed set gets an
element above all of its old members.

This is Lemma A.2 (`exists_elementary_extension_inseparable_upper_bounds'`) followed by
`exists_carrier_extension`, which places the model produced by Lemma A.2 on a countable superset
of `S.carrier` without moving the old points. -/
theorem exists_stage_successor {Ω : Type u} (hΩ : Cardinal.mk Ω = Cardinal.aleph 1)
    (S : StageModel Ω) (hcount : S.carrier.Countable) [Nonempty ↥S.carrier]
    (δ : ℕ → SetTheorySemiformula ↥S.carrier 1) (ρ : ℕ → SetTheorySemiformula ↥S.carrier 2)
    (V W : ℕ → ↥S.carrier → Prop) (hins : ∀ n, Inseparable ↥S.carrier (V n) (W n))
    (hdir : ∀ n, DirectedNoLast (dset δ n) (dlt ρ n)) :
    ∃ (T : StageModel Ω) (hsub : S.carrier ⊆ T.carrier),
      T.carrier.Countable ∧
      (∀ x y : ↥S.carrier, x ∈ y ↔ StageModel.incl hsub x ∈ StageModel.incl hsub y) ∧
      ∃ j : ElementaryMap ↥S.carrier ↥T.carrier,
        (∀ x, j x = StageModel.incl hsub x) ∧
        (∀ n, Inseparable ↥T.carrier (fun y ↦ ∃ a, V n a ∧ y = j a)
              (fun y ↦ ∃ b, W n b ∧ y = j b)) ∧
        (∀ n, ∃ d : ↥T.carrier, (δ n).Eval ![d] (fun m ↦ j m) ∧
              ∀ m : ↥S.carrier, dset δ n m → (ρ n).Eval ![j m, d] (fun m ↦ j m)) := by
  have : Countable ↥S.carrier := hcount.to_subtype
  obtain ⟨E⟩ := exists_elementary_extension_inseparable_upper_bounds' ↥S.carrier δ ρ V W hins hdir
  obtain ⟨B, hAB, e, hBcount, hcompat⟩ :=
    exists_carrier_extension hΩ S.carrier hcount E.Model (fun x ↦ E.embedding x)
      E.embedding.injective
  -- the new stage, its bijection with the model of Lemma A.2, and the inverse elementary map
  set T : StageModel Ω := StageModel.ofEquiv B e with hT
  set e' : ↥T.carrier ≃ E.Model := StageModel.ofEquivEquiv B e with he'
  set k : ElementaryMap E.Model ↥T.carrier := StageModel.ofEquivSymmMap B e with hk
  have hjk : ∀ x : E.Model, k x = e'.symm x := fun _ ↦ rfl
  have hcompat' : ∀ x : ↥S.carrier,
      e' (StageModel.incl (S := S) (T := T) hAB x) = E.embedding x := hcompat
  have hje : ∀ x : ↥S.carrier,
      k (E.embedding x) = StageModel.incl (S := S) (T := T) hAB x := by
    intro x
    rw [hjk]
    exact e'.symm_apply_eq.mpr (hcompat' x).symm
  have hcomp : (⇑e' ∘ fun m : ↥S.carrier ↦ (k.comp E.embedding) m) =
      fun m ↦ E.embedding m := by
    funext m
    show e' (k (E.embedding m)) = E.embedding m
    rw [hjk, Equiv.apply_symm_apply]
  have hiso' : ∀ x y : ↥T.carrier, e' x ∈ e' y ↔ x ∈ y := fun _ _ ↦ Iff.rfl
  refine ⟨T, hAB, hBcount, ?_, k.comp E.embedding, hje, ?_, ?_⟩
  · intro x y
    rw [StageModel.ofEquiv_mem_iff, ← he', hcompat' x, hcompat' y, E.embedding.map_mem_iff]
  · intro n
    refine ((E.inseparable n).comp_memEquiv e' hiso').congr (fun x ↦ ?_) (fun x ↦ ?_) <;>
      · constructor
        · rintro ⟨a, ha, rfl⟩
          refine ⟨a, ha, ?_⟩
          show e' (k (E.embedding a)) = E.embedding a
          rw [hjk, Equiv.apply_symm_apply]
        · rintro ⟨a, ha, hxa⟩
          refine ⟨a, ha, ?_⟩
          have : e' x = e' ((k.comp E.embedding) a) := by
            rw [hxa]
            show E.embedding a = e' (k (E.embedding a))
            rw [hjk, Equiv.apply_symm_apply]
          exact e'.injective this
  · intro n
    obtain ⟨d, hd, hdb⟩ := E.upperBound n
    refine ⟨e'.symm d, ?_, fun m hm ↦ ?_⟩
    · rw [eval_membershipIso e' hiso' (δ n) ![e'.symm d] (fun m ↦ (k.comp E.embedding) m),
        comp_vec_one, Equiv.apply_symm_apply, hcomp]
      exact hd
    · have h0 : e' ((k.comp E.embedding) m) = E.embedding m := by
        show e' (k (E.embedding m)) = E.embedding m
        rw [hjk, Equiv.apply_symm_apply]
      rw [eval_membershipIso e' hiso' (ρ n) ![(k.comp E.embedding) m, e'.symm d]
          (fun m ↦ (k.comp E.embedding) m),
        comp_vec_two, h0, Equiv.apply_symm_apply, hcomp]
      exact hdb m hm

end ZFVP
