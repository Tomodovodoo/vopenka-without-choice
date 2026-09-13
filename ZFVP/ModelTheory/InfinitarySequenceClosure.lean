import ZFVP.ModelTheory.InfinitarySequenceOperations

namespace ZFVP.Infinitary
open LO LO.FirstOrder
variable {L : Language} [L.Encodable]

namespace FragmentClosure

theorem carrier_subset_of_closed {S T : Set (TaggedFormula L)} (hS : S ⊆ T)
    (hfo : firstOrder ⊆ T) (hs : ∀ a ∈ T, successors a ⊆ T)
    (hb : ∀ a ∈ T, binders a ⊆ T) (hc : ∀ a ∈ T, ∀ b ∈ T, combine a b ∈ T) :
    carrier S ⊆ T := by
  intro a ha
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp ha
  clear ha
  induction n generalizing a with
  | zero => exact hn.elim (fun h ↦ hS h) (fun h ↦ hfo h)
  | succ n ih =>
    rcases hn with hn | (hn | hn) | hn
    · exact ih hn
    · obtain ⟨b, hbi⟩ := Set.mem_iUnion.mp hn
      obtain ⟨hbs, hab⟩ := Set.mem_iUnion.mp hbi
      exact hs b (ih hbs) hab
    · obtain ⟨b, hbi⟩ := Set.mem_iUnion.mp hn
      obtain ⟨hbs, hab⟩ := Set.mem_iUnion.mp hbi
      exact hb b (ih hbs) hab
    · obtain ⟨b, hbi⟩ := Set.mem_iUnion.mp hn
      obtain ⟨hbs, hai⟩ := Set.mem_iUnion.mp hbi
      obtain ⟨c, hci⟩ := Set.mem_iUnion.mp hai
      obtain ⟨hcs, he⟩ := Set.mem_iUnion.mp hci
      have he' : a = combine b c := he
      rw [he']
      exact hc b (ih hbs) c (ih hcs)

theorem combine_mem_carrier {S : Set (TaggedFormula L)} {a b : TaggedFormula L}
    (ha : a ∈ carrier S) (hb : b ∈ carrier S) : combine a b ∈ carrier S := by
  rcases a with ⟨n, φ⟩
  rcases b with ⟨m, ψ⟩
  by_cases h : m = n
  · subst m
    simpa [combine] using and_closed ha hb
  · simpa [combine, h] using ha

theorem carrier_mono {S T : Set (TaggedFormula L)} (h : S ⊆ T) : carrier S ⊆ carrier T :=
  carrier_subset_of_closed (h.trans (subset_carrier T)) (firstOrder_subset_carrier T)
    (fun _ ha ↦ successors_subset_carrier ha) (fun _ ha ↦ binders_subset_carrier ha)
    (fun _ ha _ hb ↦ combine_mem_carrier ha hb)

end FragmentClosure

namespace SequenceClosure

def step (S : Set (TaggedFormula L)) : Set (TaggedFormula L) :=
  S ∪ (⋃ a ∈ S, unary a) ∪ ⋃ a ∈ S, ⋃ b ∈ S, {andMap a b}

def stages (S : Set (TaggedFormula L)) : ℕ → Set (TaggedFormula L)
  | 0 => FragmentClosure.carrier S
  | n + 1 => FragmentClosure.carrier (step (stages S n))

def carrier (S : Set (TaggedFormula L)) : Set (TaggedFormula L) := ⋃ n, stages S n

theorem stages_mono (S : Set (TaggedFormula L)) : Monotone (stages S) := by
  apply monotone_nat_of_le_succ
  intro n a ha
  exact FragmentClosure.subset_carrier _ (Or.inl (Or.inl ha))

theorem stages_countable {S : Set (TaggedFormula L)} (hS : S.Countable) (n : ℕ) :
    (stages S n).Countable := by
  induction n with
  | zero => exact FragmentClosure.carrier_countable hS
  | succ n ih =>
    exact FragmentClosure.carrier_countable ((ih.union (ih.biUnion fun a _ ↦ unary_countable a)).union
      (ih.biUnion fun a _ ↦ ih.biUnion fun b _ ↦ Set.countable_singleton (andMap a b)))

theorem carrier_countable {S : Set (TaggedFormula L)} (hS : S.Countable) :
    (carrier S).Countable := Set.countable_iUnion (stages_countable hS)

theorem base_subset_carrier (S : Set (TaggedFormula L)) :
    FragmentClosure.carrier S ⊆ carrier S := Set.subset_iUnion (stages S) 0

theorem subset_carrier (S : Set (TaggedFormula L)) : S ⊆ carrier S :=
  (FragmentClosure.subset_carrier S).trans (base_subset_carrier S)

theorem stages_base_closed (S : Set (TaggedFormula L)) (n : ℕ) :
    ∃ T, stages S n = FragmentClosure.carrier T := by
  cases n with
  | zero => exact ⟨S, rfl⟩
  | succ n => exact ⟨step (stages S n), rfl⟩

theorem base_carrier_eq (S : Set (TaggedFormula L)) :
    FragmentClosure.carrier (carrier S) = carrier S := by
  apply Set.Subset.antisymm _ (FragmentClosure.subset_carrier _)
  apply FragmentClosure.carrier_subset_of_closed (Set.Subset.refl _)
  · exact (FragmentClosure.firstOrder_subset_carrier S).trans (base_subset_carrier S)
  · intro a ha b hb
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp ha
    obtain ⟨T, hT⟩ := stages_base_closed S n
    apply Set.mem_iUnion.mpr
    refine ⟨n, ?_⟩
    rw [hT] at hn ⊢
    exact FragmentClosure.successors_subset_carrier hn hb
  · intro a ha b hb
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp ha
    obtain ⟨T, hT⟩ := stages_base_closed S n
    apply Set.mem_iUnion.mpr
    refine ⟨n, ?_⟩
    rw [hT] at hn ⊢
    exact FragmentClosure.binders_subset_carrier hn hb
  · intro a ha b hb
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp ha
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hb
    have hi' := stages_mono S (Nat.le_max_left i j) hi
    have hj' := stages_mono S (Nat.le_max_right i j) hj
    obtain ⟨T, hT⟩ := stages_base_closed S (max i j)
    apply Set.mem_iUnion.mpr
    refine ⟨max i j, ?_⟩
    rw [hT] at hi' hj' ⊢
    exact FragmentClosure.combine_mem_carrier hi' hj'

theorem unary_closed {S : Set (TaggedFormula L)} {a : TaggedFormula L}
    (ha : a ∈ carrier S) : unary a ⊆ carrier S := by
  intro b hb
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp ha
  exact Set.mem_iUnion.mpr ⟨n + 1, FragmentClosure.subset_carrier _
    (Or.inl (Or.inr (Set.mem_iUnion.mpr ⟨a, Set.mem_iUnion.mpr ⟨hn, hb⟩⟩)))⟩

theorem andMap_closed {S : Set (TaggedFormula L)} {a b : TaggedFormula L}
    (ha : a ∈ carrier S) (hb : b ∈ carrier S) : andMap a b ∈ carrier S := by
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp ha
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hb
  have hi' := stages_mono S (Nat.le_max_left i j) hi
  have hj' := stages_mono S (Nat.le_max_right i j) hj
  exact Set.mem_iUnion.mpr ⟨max i j + 1, FragmentClosure.subset_carrier _
    (Or.inr (Set.mem_iUnion.mpr ⟨a, Set.mem_iUnion.mpr ⟨hi',
      Set.mem_iUnion.mpr ⟨b, Set.mem_iUnion.mpr ⟨hj', rfl⟩⟩⟩⟩))⟩

theorem conj_neg_closed {S : Set (TaggedFormula L)} {n} {f : ℕ → Formula L n}
    (hf : ⟨n, .conj f⟩ ∈ carrier S) : ⟨n, .conj fun i ↦ .neg (f i)⟩ ∈ carrier S :=
  unary_closed hf (Or.inl rfl)

theorem conj_exs_closed {S : Set (TaggedFormula L)} {n} {f : ℕ → Formula L (n + 1)}
    (hf : ⟨n + 1, .conj f⟩ ∈ carrier S) : ⟨n, .conj fun i ↦ .exs (f i)⟩ ∈ carrier S :=
  unary_closed hf (Or.inr (Or.inl rfl))

theorem conj_q_closed {S : Set (TaggedFormula L)} {n} {f : ℕ → Formula L (n + 1)}
    (hf : ⟨n + 1, .conj f⟩ ∈ carrier S) : ⟨n, .conj fun i ↦ .q (f i)⟩ ∈ carrier S :=
  unary_closed hf (Or.inr (Or.inr rfl))

theorem conj_and_closed {S : Set (TaggedFormula L)} {n} {f : ℕ → Formula L n} {ψ : Formula L n}
    (hf : ⟨n, .conj f⟩ ∈ carrier S) (hψ : ⟨n, ψ⟩ ∈ carrier S) :
    ⟨n, .conj fun i ↦ ψ.and (f i)⟩ ∈ carrier S := by
  simpa [andMap] using andMap_closed hf hψ

theorem neg_closed {S : Set (TaggedFormula L)} {n} {φ : Formula L n}
    (hφ : ⟨n, φ⟩ ∈ carrier S) : ⟨n, .neg φ⟩ ∈ carrier S := by
  rw [← base_carrier_eq S] at hφ ⊢
  exact FragmentClosure.neg_closed hφ

theorem conj_disj_closed {S : Set (TaggedFormula L)} {n} {f : ℕ → Formula L n}
    (hf : ⟨n, .conj f⟩ ∈ carrier S) : ⟨n, Formula.disj f⟩ ∈ carrier S :=
  neg_closed (conj_neg_closed hf)

open HenkinLanguage

theorem carrier_supported {S : Set (TaggedFormula (limit L))}
    (hS : ∀ a ∈ S, FiniteSupport a.2) {a : TaggedFormula (limit L)}
    (ha : a ∈ carrier S) : FiniteSupport a.2 := by
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp ha
  clear ha
  induction n generalizing a with
  | zero => exact finiteSupport_fragment hS hn
  | succ n ih =>
    apply finiteSupport_fragment (fun b hb ↦ ?_) hn
    rcases hb with (hb | hb) | hb
    · exact ih hb
    · obtain ⟨c, hci⟩ := Set.mem_iUnion.mp hb
      obtain ⟨hcs, hbc⟩ := Set.mem_iUnion.mp hci
      exact unary_supported (ih hcs) hbc
    · obtain ⟨c, hci⟩ := Set.mem_iUnion.mp hb
      obtain ⟨hcs, hdi⟩ := Set.mem_iUnion.mp hci
      obtain ⟨d, hdi⟩ := Set.mem_iUnion.mp hdi
      obtain ⟨hds, he⟩ := Set.mem_iUnion.mp hdi
      have he' : b = andMap c d := he
      rw [he']
      exact andMap_supported (ih hcs) (ih hds)

end SequenceClosure
end ZFVP.Infinitary

