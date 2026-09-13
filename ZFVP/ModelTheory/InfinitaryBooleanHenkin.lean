import ZFVP.ModelTheory.InfinitaryKeislerConsistency

namespace ZFVP.Infinitary
open LO LO.FirstOrder
namespace KeislerDerivation
variable {L : Language} [L.Eq]

/-- One finite extension decides a sentence and, if it rejects a countable conjunction,
records a particular rejected conjunct. -/
def BooleanStep (Γ : Set (Sentence L)) (φ : Sentence L) (Δ : Set (Sentence L)) : Prop :=
  Γ ⊆ Δ ∧ (Γ.Countable → Δ.Countable) ∧ Consistent Δ ∧
  (φ ∈ Δ ∨ .neg φ ∈ Δ) ∧
  ∀ f : ℕ → Sentence L, φ = .conj f → (.conj f ∈ Δ ∨ ∃ i, .neg (f i) ∈ Δ)

theorem exists_booleanStep (Γ : Set (Sentence L)) (hΓ : Consistent Γ) (φ : Sentence L) :
    ∃ Δ, BooleanStep Γ φ Δ := by
  classical
  rcases consistent_decide hΓ φ with hp | hn
  · refine ⟨insert φ Γ, Set.subset_insert _ _, fun hc ↦ hc.insert _, hp,
      Or.inl (Set.mem_insert _ _), ?_⟩
    intro f hf
    exact Or.inl (hf ▸ Set.mem_insert φ Γ)
  · by_cases hconj : ∃ f : ℕ → Sentence L, φ = .conj f
    · obtain ⟨f, rfl⟩ := hconj
      obtain ⟨i, hi⟩ := consistent_neg_conj_witness hn f (of_mem (Set.mem_insert _ _))
      refine ⟨insert (.neg (f i)) (insert (.neg (.conj f)) Γ),
        (Set.subset_insert _ _).trans (Set.subset_insert _ _),
        fun hc ↦ (hc.insert _).insert _, hi, Or.inr (Or.inr (Or.inl rfl)), ?_⟩
      intro g hg
      cases Formula.conj.inj hg
      exact Or.inr ⟨i, Set.mem_insert _ _⟩
    · refine ⟨insert (.neg φ) Γ, Set.subset_insert _ _, fun hc ↦ hc.insert _, hn,
        Or.inr (Set.mem_insert _ _), ?_⟩
      intro f hf
      exact (hconj ⟨f, hf⟩).elim

open Classical in
noncomputable def booleanStep (Γ : Set (Sentence L)) (φ : Sentence L) : Set (Sentence L) :=
  if h : Consistent Γ then (exists_booleanStep Γ h φ).choose else Γ

theorem booleanStep_spec (Γ : Set (Sentence L)) (hΓ : Consistent Γ) (φ : Sentence L) :
    BooleanStep Γ φ (booleanStep Γ φ) := by
  classical
  rw [booleanStep, dif_pos hΓ]
  exact (exists_booleanStep Γ hΓ φ).choose_spec

noncomputable def booleanStages (Γ : Set (Sentence L)) (e : ℕ → Sentence L) : ℕ → Set (Sentence L)
  | 0 => Γ
  | n + 1 => booleanStep (booleanStages Γ e n) (e n)

theorem booleanStages_consistent (Γ : Set (Sentence L)) (hc : Consistent Γ)
    (e : ℕ → Sentence L) (n : ℕ) : Consistent (booleanStages Γ e n) := by
  induction n with
  | zero => exact hc
  | succ n ih => exact (booleanStep_spec _ ih _).2.2.1

theorem booleanStages_step_subset (Γ : Set (Sentence L)) (hc : Consistent Γ)
    (e : ℕ → Sentence L) (n : ℕ) : booleanStages Γ e n ⊆ booleanStages Γ e (n + 1) :=
  (booleanStep_spec _ (booleanStages_consistent Γ hc e n) _).1

theorem booleanStages_mono (Γ : Set (Sentence L)) (hc : Consistent Γ) (e : ℕ → Sentence L) :
    Monotone (booleanStages Γ e) :=
  monotone_nat_of_le_succ (booleanStages_step_subset Γ hc e)

theorem booleanStages_countable (Γ : Set (Sentence L)) (hc : Consistent Γ)
    (hcount : Γ.Countable) (e : ℕ → Sentence L) (n : ℕ) : (booleanStages Γ e n).Countable := by
  induction n with
  | zero => exact hcount
  | succ n ih => exact (booleanStep_spec _ (booleanStages_consistent Γ hc e n) _).2.1 ih

/-- Each finite part of an increasing union appears together in a single stage. -/
theorem finite_subset_booleanStages (Γ : Set (Sentence L)) (hc : Consistent Γ)
    (e : ℕ → Sentence L) (s : Finset (Sentence L))
    (hs : ∀ φ ∈ s, φ ∈ ⋃ n, booleanStages Γ e n) :
    ∃ n, ∀ φ ∈ s, φ ∈ booleanStages Γ e n := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | @insert φ s hφ ih =>
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hs φ (Finset.mem_insert_self _ _))
      obtain ⟨j, hj⟩ := ih (fun ψ hψ ↦ hs ψ (Finset.mem_insert_of_mem hψ))
      refine ⟨max i j, fun ψ hψ ↦ ?_⟩
      rcases Finset.mem_insert.mp hψ with rfl | hψ
      · exact booleanStages_mono Γ hc e (le_max_left _ _) hi
      · exact booleanStages_mono Γ hc e (le_max_right _ _) (hj ψ hψ)

/-- The countable Boolean part of a Henkin construction. The union is finitely
consistent; no unsupported assertion of full infinitary consistency at the union is made. -/
structure BooleanHenkinExtension (Γ F : Set (Sentence L)) where
  carrier : Set (Sentence L)
  countable : carrier.Countable
  includes : Γ ⊆ carrier
  finite_consistent : ∀ s : Finset (Sentence L), (∀ φ ∈ s, φ ∈ carrier) → Consistent (s : Set (Sentence L))
  decides : ∀ φ ∈ F, φ ∈ carrier ∨ .neg φ ∈ carrier
  conjunction_witness : ∀ f : ℕ → Sentence L, .conj f ∈ F →
    .conj f ∈ carrier ∨ ∃ i, .neg (f i) ∈ carrier

/-- A countable prescribed collection of sentences can be decided with all negated
conjunction witnesses while retaining consistency of every finite subset. -/
theorem exists_booleanHenkinExtension (Γ F : Set (Sentence L))
    (hΓ : Γ.Countable) (hF : F.Countable) (hc : Consistent Γ) :
    Nonempty (BooleanHenkinExtension Γ F) := by
  classical
  obtain ⟨e, he⟩ := (hF.insert (.fo .verum)).exists_eq_range (Set.insert_nonempty _ _)
  let H : Set (Sentence L) := ⋃ n, booleanStages Γ e n
  have hspec (n : ℕ) := booleanStep_spec _ (booleanStages_consistent Γ hc e n) (e n)
  have hcov : ∀ φ ∈ F, ∃ n, e n = φ := by
    intro φ hφ
    apply Set.mem_range.mp
    rw [← he]
    exact Set.mem_insert_of_mem _ hφ
  refine ⟨⟨H, Set.countable_iUnion (booleanStages_countable Γ hc hΓ e),
    Set.subset_iUnion (fun n ↦ booleanStages Γ e n) 0, ?_, ?_, ?_⟩⟩
  · intro s hs
    obtain ⟨n, hn⟩ := finite_subset_booleanStages Γ hc e s hs
    exact consistent_mono (fun φ hφ ↦ hn φ hφ) (booleanStages_consistent Γ hc e n)
  · intro φ hφ
    obtain ⟨n, rfl⟩ := hcov φ hφ
    rcases (hspec n).2.2.2.1 with h | h
    · exact Or.inl (Set.mem_iUnion.mpr ⟨n + 1, h⟩)
    · exact Or.inr (Set.mem_iUnion.mpr ⟨n + 1, h⟩)
  · intro f hf
    obtain ⟨n, hn⟩ := hcov (.conj f) hf
    rcases (hspec n).2.2.2.2 f hn with h | ⟨i, hi⟩
    · exact Or.inl (Set.mem_iUnion.mpr ⟨n + 1, h⟩)
    · exact Or.inr ⟨i, Set.mem_iUnion.mpr ⟨n + 1, hi⟩⟩

namespace BooleanHenkinExtension
variable {Γ F : Set (Sentence L)} (H : BooleanHenkinExtension Γ F)

theorem not_both (φ : Sentence L) (hφ : φ ∈ H.carrier) (hn : .neg φ ∈ H.carrier) : False := by
  classical
  let s : Finset (Sentence L) := {φ, .neg φ}
  have hc : Consistent (s : Set (Sentence L)) := H.finite_consistent s (by
    intro ψ hψ
    simp only [s, Finset.mem_insert, Finset.mem_singleton] at hψ
    rcases hψ with rfl | rfl <;> assumption)
  exact hc ((of_mem (by simp [s] : φ ∈ (s : Set (Sentence L)))).contradiction
    (of_mem (by simp [s])))

theorem neg_mem_iff {φ : Sentence L} (hφ : φ ∈ F) :
    .neg φ ∈ H.carrier ↔ φ ∉ H.carrier := by
  constructor
  · exact fun hn hp ↦ H.not_both φ hp hn
  · intro hn
    exact (H.decides φ hφ).resolve_left hn

theorem conj_mem_iff (f : ℕ → Sentence L) (hf : .conj f ∈ F)
    (hfi : ∀ i, f i ∈ F) : .conj f ∈ H.carrier ↔ ∀ i, f i ∈ H.carrier := by
  classical
  constructor
  · intro hc i
    by_contra hi
    have hn := (H.neg_mem_iff (hfi i)).mpr hi
    let s : Finset (Sentence L) := {.conj f, .neg (f i)}
    have hs : Consistent (s : Set (Sentence L)) := H.finite_consistent s (by
      intro ψ hψ
      simp only [s, Finset.mem_insert, Finset.mem_singleton] at hψ
      rcases hψ with rfl | rfl <;> assumption)
    have hd : KeislerDerivation (s : Set (Sentence L)) (f i) :=
      .mp (.boolean (.projection f i)) (of_mem (by simp [s]))
    exact hs (hd.contradiction (of_mem (by simp [s])))
  · intro h
    rcases H.conjunction_witness f hf with hc | ⟨i, hi⟩
    · exact hc
    · exact (H.not_both _ (h i) hi).elim

end BooleanHenkinExtension
end KeislerDerivation
end ZFVP.Infinitary

