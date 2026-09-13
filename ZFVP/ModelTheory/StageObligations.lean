import ZFVP.ModelTheory.SeparatingTypesOmitted

/-! # The bookkeeping input of Enayat's Lemma A.2

`ZFVP.exists_elementary_extension_inseparable_upper_bounds'` takes `ω`-indexed families of
definable directed sets with no last element and of inseparable pairs. Enayat feeds it *all* the
definable directed sets with no last element of the current stage; that is legitimate because the
stage is countable, so there are only countably many formulas with parameters from it.

This file supplies that step:

* `ZFVP.countable_setTheorySemiformula`, countability of `SetTheorySemiformula M n` for countable
  `M`, taken from Foundation's `Encodable (Semiformula L ξ n)` after `Encodable.ofCountable`;
* `ZFVP.exists_directed_enumeration`, an `ω`-indexed family listing every pair of formulas that
  defines a directed set with no last element;
* `ZFVP.exists_inseparable_enumeration`, the same for a countable set of inseparable pairs;
* `ZFVP.exists_extension_all_directed`, the two put together and handed to Lemma A.2, with the
  upper bound clause stated for every definable directed set with no last element of `M`.

Both enumerations need a default value to pad with, and in a nonempty set structure both defaults
are available without any set-theoretic axiom: `⊤` defines the whole of `M` with the total relation
as its order (`ZFVP.directedNoLast_top`), and the pair `(True, True)` is inseparable, since a
definable set would have to contain and miss the same element (`ZFVP.inseparable_true`). So no
hypothesis such as `O.Nonempty` or an explicit default inseparable pair is needed.
-/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

universe u

/-! ## Countability of the syntax over countable parameters -/

/-- The formulas of `ℒₛₑₜ` with free variables from a countable `M` form a countable type.
Foundation encodes `Semiformula L ξ n` whenever the symbols of `L` and the type `ξ` are encodable;
`ℒₛₑₜ` has encodable symbols, and `Encodable.ofCountable` turns `Countable M` into `Encodable M`. -/
instance (priority := low) countable_setTheorySemiformula {M : Type u} [Countable M] {n : ℕ} :
    Countable (SetTheorySemiformula M n) := by
  classical
  let _ : Encodable M := Encodable.ofCountable M
  infer_instance

/-! ## The two defaults -/

section Defaults

variable (M : Type u) [SetStructure M] [Nonempty M]

/-- `⊤` defines the whole of `M`, and `⊤` in two variables defines the total relation on it; that
is a directed set with no last element. This is the value the enumeration below pads with. -/
theorem directedNoLast_top :
    DirectedNoLast (fun x : M ↦ (⊤ : SetTheorySemiformula M 1).Eval ![x] id)
      (fun x y : M ↦ (⊤ : SetTheorySemiformula M 2).Eval ![x, y] id) := by
  refine ⟨⟨Classical.arbitrary M, by simp⟩, fun _ _ _ _ _ _ _ _ ↦ by simp, fun x y _ _ ↦ ?_⟩
  exact ⟨Classical.arbitrary M, by simp, by simp, by simp⟩

/-- `True` and `True` are inseparable in a nonempty model: a definable set containing every element
and missing every element cannot exist. This is the value the enumeration below pads with. -/
theorem inseparable_true : Inseparable M (fun _ ↦ True) (fun _ ↦ True) := by
  rintro ⟨X, -, hV, hW⟩
  exact hW (Classical.arbitrary M) trivial (hV (Classical.arbitrary M) trivial)

end Defaults

/-! ## The enumerations -/

variable {M : Type u} [SetStructure M] [Nonempty M] [Countable M]

/-- Every pair of formulas defining a directed set with no last element in `M` occurs in an
`ω`-indexed family all of whose members define such a set. The pairs of formulas form a countable
type, and the pairs that are not directed with no last element are replaced by `(⊤, ⊤)`. -/
theorem exists_directed_enumeration :
    ∃ (δ : ℕ → SetTheorySemiformula M 1) (ρ : ℕ → SetTheorySemiformula M 2),
      (∀ n, DirectedNoLast (dset δ n) (dlt ρ n)) ∧
      ∀ (d : SetTheorySemiformula M 1) (r : SetTheorySemiformula M 2),
        DirectedNoLast (fun x ↦ d.Eval ![x] id) (fun x y ↦ r.Eval ![x, y] id) →
          ∃ n, δ n = d ∧ ρ n = r := by
  classical
  set P : SetTheorySemiformula M 1 × SetTheorySemiformula M 2 → Prop := fun p ↦
    DirectedNoLast (fun x ↦ p.1.Eval ![x] id) (fun x y ↦ p.2.Eval ![x, y] id) with hP
  have hne : Nonempty (SetTheorySemiformula M 1 × SetTheorySemiformula M 2) := ⟨(⊤, ⊤)⟩
  obtain ⟨e, he⟩ := exists_surjective_nat (SetTheorySemiformula M 1 × SetTheorySemiformula M 2)
  obtain ⟨pick, hpickP, hpickCov⟩ :
      ∃ pick : ℕ → SetTheorySemiformula M 1 × SetTheorySemiformula M 2,
        (∀ n, P (pick n)) ∧ ∀ p, P p → ∃ n, pick n = p := by
    refine ⟨fun n ↦ if P (e n) then e n else (⊤, ⊤), fun n ↦ ?_, fun p hp ↦ ?_⟩
    · show P (if P (e n) then e n else (⊤, ⊤))
      split_ifs with h
      · exact h
      · exact directedNoLast_top M
    · obtain ⟨n, hn⟩ := he p
      refine ⟨n, ?_⟩
      show (if P (e n) then e n else (⊤, ⊤)) = p
      rw [hn]
      split_ifs
      rfl
  refine ⟨fun n ↦ (pick n).1, fun n ↦ (pick n).2, fun n ↦ hpickP n, fun d r hdr ↦ ?_⟩
  obtain ⟨n, hn⟩ := hpickCov (d, r) hdr
  exact ⟨n, congrArg Prod.fst hn, congrArg Prod.snd hn⟩

omit [Countable M] in
/-- A countable set of inseparable pairs is covered by an `ω`-indexed family of inseparable pairs.
The empty case is padded with the pair `(True, True)`, which is inseparable in a nonempty model, so
no nonemptiness hypothesis and no default pair have to be supplied by the caller. -/
theorem exists_inseparable_enumeration (O : Set ((M → Prop) × (M → Prop)))
    (hO : O.Countable) (hins : ∀ p ∈ O, Inseparable M p.1 p.2) :
    ∃ V W : ℕ → M → Prop, (∀ n, Inseparable M (V n) (W n)) ∧
      ∀ p ∈ O, ∃ n, V n = p.1 ∧ W n = p.2 := by
  classical
  rcases O.eq_empty_or_nonempty with rfl | hne
  · exact ⟨fun _ _ ↦ True, fun _ _ ↦ True, fun _ ↦ inseparable_true M, by simp⟩
  · obtain ⟨f, hf⟩ := hO.exists_eq_range hne
    refine ⟨fun n ↦ (f n).1, fun n ↦ (f n).2, fun n ↦ hins (f n) ?_, fun p hp ↦ ?_⟩
    · rw [hf]; exact Set.mem_range_self n
    · rw [hf] at hp
      obtain ⟨n, rfl⟩ := hp
      exact ⟨n, rfl, rfl⟩

/-! ## Lemma A.2 for all the definable directed sets at once -/

/-- Enayat's Lemma A.2 in the form the construction uses it: from a countable set `O` of
inseparable pairs of subsets of a countable model `M` there is a countable elementary extension in
which every pair of `O` is still inseparable and *every* definable directed set with no last
element of `M` has an element above all of its old elements. -/
theorem exists_extension_all_directed (O : Set ((M → Prop) × (M → Prop))) (hO : O.Countable)
    (hins : ∀ p ∈ O, Inseparable M p.1 p.2) :
    ∃ (N : Type u) (_ : SetStructure N) (_ : Nonempty N) (_ : Countable N)
      (j : ElementaryMap M N),
      (∀ p ∈ O, Inseparable N (fun y ↦ ∃ a, p.1 a ∧ y = j a) (fun y ↦ ∃ b, p.2 b ∧ y = j b)) ∧
      ∀ (d : SetTheorySemiformula M 1) (r : SetTheorySemiformula M 2),
        DirectedNoLast (fun x ↦ d.Eval ![x] id) (fun x y ↦ r.Eval ![x, y] id) →
          ∃ e : N, d.Eval ![e] (fun m ↦ j m) ∧
            ∀ m : M, d.Eval ![m] id → r.Eval ![j m, e] (fun m ↦ j m) := by
  classical
  obtain ⟨δ, ρ, hdir, hcov⟩ := exists_directed_enumeration (M := M)
  obtain ⟨V, W, hVW, hOcov⟩ := exists_inseparable_enumeration O hO hins
  obtain ⟨E⟩ := exists_elementary_extension_inseparable_upper_bounds' M δ ρ V W hVW hdir
  refine ⟨E.Model, E.setStructure, E.nonempty, E.countable, E.embedding, fun p hp ↦ ?_,
    fun d r hdr ↦ ?_⟩
  · obtain ⟨n, hV, hW⟩ := hOcov p hp
    have := E.inseparable n
    rw [hV, hW] at this
    exact this
  · obtain ⟨n, hd, hr⟩ := hcov d r hdr
    obtain ⟨x, hmem, hbound⟩ := E.upperBound n
    rw [hd] at hmem
    refine ⟨x, hmem, fun m hm ↦ ?_⟩
    have := hbound m (by rw [dset, hd]; exact hm)
    rw [hr] at this
    exact this

end ZFVP
