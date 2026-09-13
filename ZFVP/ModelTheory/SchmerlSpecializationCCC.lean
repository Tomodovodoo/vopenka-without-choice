import ZFVP.ModelTheory.SchmerlStrictSpecialization
import Mathlib.Order.Filter.Cocardinal
import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Data.Set.Card

/-! The countable chain condition for finite strict specializations of a tree
whose chains are countable. The proof uses induction on condition size and the
uniform-ultrafilter argument for the case of countable occurrence fibers.
-/

namespace ZFVP.Schmerl

open Set Filter

universe u v

variable {T : Type u} [PartialOrder T]

/-- The uniform-ultrafilter step in the specializing-forcing proof. If a
finite tuple family has countable occurrence fibers and every two tuples
contain comparable nodes, the family itself is countable. -/
theorem countable_of_sparse_cross_comparability (hT : IsTreeOrder T)
    (hchains : ∀ C : Set T, IsChain (· ≤ ·) C → C.Countable)
    {A : Type v} {n : ℕ} (t : A → Fin (n + 1) → T)
    (hsmall : ∀ x, {a | ∃ i, t a i = x}.Countable)
    (hcross : ∀ a b, a ≠ b → ∃ i j, t a i ≤ t b j ∨ t b j ≤ t a i) :
    Countable A := by
  classical
  by_contra hcount
  have hunc : ¬ (Set.univ : Set A).Countable := fun h ↦ hcount (Set.countable_univ_iff.mp h)
  let : Filter.NeBot (Filter.cocountable : Filter A) := ⟨fun hbot ↦ by
    have hempty := Filter.empty_mem_iff_bot.mpr hbot
    exact hunc (by simpa only [Set.compl_empty] using Filter.mem_cocountable.mp hempty)⟩
  let U : Ultrafilter A := Ultrafilter.of Filter.cocountable
  have hbelow (x : T) : (Set.Iic x).Countable :=
    hchains _ (fun _ ha _ hb _ ↦ hT ha hb)
  have hbad (a : A) : {b | ∃ i j, t b j ≤ t a i}.Countable := by
    have hc : (⋃ i : Fin (n + 1), ⋃ x ∈ Set.Iic (t a i), {b | ∃ j, t b j = x}).Countable :=
      Set.countable_iUnion (fun i ↦ (hbelow (t a i)).biUnion (fun x _ ↦ hsmall x))
    apply hc.mono
    rintro b ⟨i, j, hij⟩
    exact Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨t b j,
      Set.mem_iUnion.mpr ⟨hij, j, rfl⟩⟩⟩
  have hchoice (a : A) : ∃ i j, ∀ᶠ b in U, t a i ≤ t b j := by
    have hgood : ∀ᶠ b in U, ¬ ∃ i j, t b j ≤ t a i := by
      apply Ultrafilter.of_le Filter.cocountable
      exact Filter.mem_cocountable.mpr (by
        simpa only [Set.compl_ofPred, not_not] using hbad a)
    have hex : ∀ᶠ b in U, ∃ i j, t a i ≤ t b j := by
      filter_upwards [hgood] with b hb
      have hab : a ≠ b := by
        rintro rfl
        exact hb ⟨0, 0, le_rfl⟩
      obtain ⟨i, j, hij | hji⟩ := hcross a b hab
      · exact ⟨i, j, hij⟩
      · exact (hb ⟨i, j, hji⟩).elim
    obtain ⟨i, hi⟩ := Ultrafilter.eventually_exists_iff.mp hex
    obtain ⟨j, hj⟩ := Ultrafilter.eventually_exists_iff.mp hi
    exact ⟨i, j, hj⟩
  choose left right hchoice using hchoice
  let C (j : Fin (n + 1)) : Set T := {x | ∃ a, right a = j ∧ t a (left a) = x}
  have hC (j : Fin (n + 1)) : (C j).Countable := by
    apply hchains
    rintro x ⟨a, ha, rfl⟩ y ⟨b, hb, rfl⟩ _
    obtain ⟨c, hca, hcb⟩ := ((hchoice a).and (hchoice b)).exists
    rw [ha] at hca
    rw [hb] at hcb
    exact hT hca hcb
  have hrange : (Set.range (fun a ↦ t a (left a))).Countable := by
    apply (Set.countable_iUnion hC).mono
    rintro x ⟨a, rfl⟩
    exact Set.mem_iUnion.mpr ⟨right a, a, rfl, rfl⟩
  apply hunc
  have hc := hrange.biUnion (fun x _ ↦ hsmall x)
  apply hc.mono
  intro a _
  exact Set.mem_iUnion.mpr ⟨t a (left a), Set.mem_iUnion.mpr
    ⟨Set.mem_range_self a, left a, rfl⟩⟩

namespace StrictCondition

/-- Each fixed-size antichain of finite strict-coloring conditions is countable. -/
theorem countable_antichain_of_ncard (hT : IsTreeOrder T)
    (hchains : ∀ C : Set T, IsChain (· ≤ ·) C → C.Countable) (n : ℕ)
    (A : Set (StrictCondition T))
    (hA : A.Pairwise (fun p q ↦ ¬ Compatible p q))
    (hsize : ∀ p ∈ A, p.graph.ncard = n) : A.Countable := by
  classical
  induction n generalizing A with
  | zero =>
      apply (Set.countable_singleton (⊤ : StrictCondition T)).mono
      intro p hp
      apply Set.mem_singleton_iff.mpr
      apply ext
      exact (Set.ncard_eq_zero p.finite).mp (hsize p hp)
  | succ n ih =>
      have hpair (a : T × ℕ) : {p ∈ A | a ∈ p.graph}.Countable := by
        let B : Set (StrictCondition T) := {p ∈ A | a ∈ p.graph}
        have hanti : ((fun p ↦ p.erase a) '' B).Pairwise
            (fun p q ↦ ¬ Compatible p q) := by
          rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩ hne hcomp
          exact hA hp.1 hq.1 (fun heq ↦ hne (congrArg (fun r ↦ r.erase a) heq))
            (compatible_of_erase hp.2 hq.2 hcomp)
        have hnewsize : ∀ q ∈ (fun p ↦ p.erase a) '' B, q.graph.ncard = n := by
          rintro _ ⟨p, hp, rfl⟩
          rw [graph_erase, Set.ncard_sdiff_singleton_of_mem hp.2, hsize p hp.1]
          exact Nat.add_sub_cancel_right n 1
        have hc := ih _ hanti hnewsize
        exact Set.countable_of_injective_of_countable_image
          ((erase_injOn a).mono (fun _ hp ↦ hp.2)) hc
      have hnode (x : T) : {p ∈ A | ∃ m, (x, m) ∈ p.graph}.Countable := by
        apply (Set.countable_iUnion (fun m ↦ hpair (x, m))).mono
        rintro p ⟨hp, m, hm⟩
        exact Set.mem_iUnion.mpr ⟨m, hp, hm⟩
      let enum (p : A) : Fin (n + 1) ≃ p.val.graph := by
        let : Fintype p.val.graph := p.val.finite.fintype
        exact (Fintype.equivFinOfCardEq (by
          simpa only [Set.fintypeCard_eq_ncard] using hsize p.val p.property)).symm
      let t (p : A) (i : Fin (n + 1)) : T := (enum p i).val.1
      have hsmall (x : T) : {p | ∃ i, t p i = x}.Countable := by
        apply ((hnode x).preimage Subtype.val_injective).mono
        rintro p ⟨i, hi⟩
        refine ⟨p.property, (enum p i).val.2, ?_⟩
        have hm := (enum p i).property
        have heq : (enum p i).val = (x, (enum p i).val.2) := Prod.ext hi rfl
        exact heq ▸ hm
      have hcross : ∀ p q : A, p ≠ q →
          ∃ i j, t p i ≤ t q j ∨ t q j ≤ t p i := by
        intro p q hpq
        have hinc := hA p.property q.property (fun heq ↦ hpq (Subtype.ext heq))
        obtain ⟨a, ha, b, hb, hab⟩ := exists_comparable_of_not_compatible hinc
        obtain ⟨i, hi⟩ := (enum p).surjective ⟨a, ha⟩
        obtain ⟨j, hj⟩ := (enum q).surjective ⟨b, hb⟩
        refine ⟨i, j, ?_⟩
        simpa only [t, hi, hj] using hab
      exact Set.countable_coe_iff.mp
        (countable_of_sparse_cross_comparability hT hchains t hsmall hcross)

/-- Baumgartner-Malitz-Reinhardt: finite strict specializations of a tree with
only countable chains satisfy the countable chain condition. -/
theorem countable_antichains (hT : IsTreeOrder T)
    (hchains : ∀ C : Set T, IsChain (· ≤ ·) C → C.Countable)
    (A : Set (StrictCondition T))
    (hA : A.Pairwise (fun p q ↦ ¬ Compatible p q)) : A.Countable := by
  have hc (n : ℕ) : {p ∈ A | p.graph.ncard = n}.Countable :=
    countable_antichain_of_ncard hT hchains n _
      (hA.mono (fun _ hp ↦ hp.1)) (fun _ hp ↦ hp.2)
  apply (Set.countable_iUnion hc).mono
  intro p hp
  exact Set.mem_iUnion.mpr ⟨p.graph.ncard, hp, rfl⟩

end StrictCondition

end ZFVP.Schmerl
