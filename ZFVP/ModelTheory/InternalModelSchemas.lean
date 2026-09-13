import ZFVP.SetTheory.RankZF
import ZFVP.Syntax.DeltaOneMembershipTruth

/-! Separation, Collection and Replacement for all internal membership formula codes. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def InternalSeparation (A : V) : Prop :=
  ∀ n ∈ (ω : V), ∀ φ, IsMembershipFormulaCode (succ n) φ → ∀ b ∈ A ^ n,
    ∀ a ∈ A, ∃ c ∈ A, ∀ x ∈ A,
      (x ∈ c ↔ x ∈ a ∧ MembershipSatisfies A (succ n) φ (assignmentPrepend n b x))

def InternalCollection (A : V) : Prop :=
  ∀ n ∈ (ω : V), ∀ φ, IsMembershipFormulaCode (succ (succ n)) φ → ∀ b ∈ A ^ n,
    ∀ a ∈ A, (∀ x ∈ A, x ∈ a → ∃ y ∈ A,
      MembershipSatisfies A (succ (succ n)) φ (assignmentPrepend (succ n) (assignmentPrepend n b y) x)) →
      ∃ c ∈ A, ∀ x ∈ A, x ∈ a → ∃ y ∈ A, y ∈ c ∧
        MembershipSatisfies A (succ (succ n)) φ (assignmentPrepend (succ n) (assignmentPrepend n b y) x)

def InternalReplacement (A : V) : Prop :=
  ∀ n ∈ (ω : V), ∀ φ, IsMembershipFormulaCode (succ (succ n)) φ → ∀ b ∈ A ^ n,
    ∀ a ∈ A, (∀ x ∈ A, x ∈ a → ∃! y, y ∈ A ∧
      MembershipSatisfies A (succ (succ n)) φ (assignmentPrepend (succ n) (assignmentPrepend n b y) x)) →
      ∃ c ∈ A, ∀ y ∈ A, (y ∈ c ↔ ∃ x ∈ A, x ∈ a ∧
        MembershipSatisfies A (succ (succ n)) φ (assignmentPrepend (succ n) (assignmentPrepend n b y) x))

instance internalSeparation_definable : ℒₛₑₜ-predicate[V] InternalSeparation := by
  unfold InternalSeparation
  definability

instance internalCollection_definable : ℒₛₑₜ-predicate[V] InternalCollection := by
  unfold InternalCollection
  definability

instance internalReplacement_definable : ℒₛₑₜ-predicate[V] InternalReplacement := by
  unfold InternalReplacement
  definability

theorem rank_internalSeparation {θ : V} [IsOrdinal θ] (hs : ∀ β ∈ θ, succ β ∈ θ) :
    InternalSeparation (hierarchy θ) := by
  intro n _ φ _ b _ a ha
  let c := {x ∈ a ; MembershipSatisfies (hierarchy θ) (succ n) φ (assignmentPrepend n b x)}
  refine ⟨c, subset_mem_hierarchy_limit hs ha (show c ⊆ a from sep_subset), ?_⟩
  intro x _
  exact mem_sep_iff

theorem rank_internalCollection {θ : V} [IsOrdinal θ] (hs : ∀ β ∈ θ, succ β ∈ θ)
    (hθ : NoLowRankCofinalMaps θ) : InternalCollection (hierarchy θ) := by
  intro n _ φ _ b _ a ha hxy
  obtain ⟨c, hc, hw⟩ := hθ.collection hs ha
    (fun x y ↦ MembershipSatisfies (hierarchy θ) (succ (succ n)) φ (assignmentPrepend (succ n) (assignmentPrepend n b y) x))
    (by definability) (fun x hx ↦ hxy x ((hierarchy_transitive θ).mem_trans hx ha) hx)
  refine ⟨c, hc, ?_⟩
  intro x _ hx
  obtain ⟨y, hy, hxy⟩ := hw x hx
  exact ⟨y, (hierarchy_transitive θ).mem_trans hy hc, hy, hxy⟩

theorem rank_internalReplacement {θ : V} [IsOrdinal θ] (hs : ∀ β ∈ θ, succ β ∈ θ)
    (hθ : NoLowRankCofinalMaps θ) : InternalReplacement (hierarchy θ) := by
  intro n _ φ _ b _ a ha hxy
  obtain ⟨c, hc, hw⟩ := hθ.replacement hs ha
    (fun x y ↦ MembershipSatisfies (hierarchy θ) (succ (succ n)) φ (assignmentPrepend (succ n) (assignmentPrepend n b y) x))
    (by definability) (fun x hx ↦ hxy x ((hierarchy_transitive θ).mem_trans hx ha) hx)
  refine ⟨c, hc, ?_⟩
  intro y hy
  rw [hw y hy]
  exact ⟨fun ⟨x, hx, hxy⟩ ↦ ⟨x, (hierarchy_transitive θ).mem_trans hx ha, hx, hxy⟩,
    fun ⟨x, _, hx, hxy⟩ ↦ ⟨x, hx, hxy⟩⟩

end ZFVP
