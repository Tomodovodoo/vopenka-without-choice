import ZFVP.ModelTheory.SchmerlInternalRenaming
import ZFVP.ModelTheory.SchmerlInternalInfinitaryFragmentAgreement
import ZFVP.Syntax.MembershipSwap

/-! Actual internal syntax swapping the first two bound variables. The
truth equation can be used in any valid fragment containing the result,
so the original and swapped formulas need not start in the same fragment. -/

namespace ZFVP.Infinitary.Internal
open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance shiftTwoIndices_definable : ℒₛₑₜ-function₁[V] shiftTwoIndices := by
  have h : ℒₛₑₜ-relation[V] (fun r n ↦ ∀ p, p ∈ r ↔ ∃ i ∈ n, p = ⟨i, succ (succ i)⟩ₖ) := by
    definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = shiftTwoIndices (v 1) ↔ _
  rw [mem_ext_iff]
  simp only [shiftTwoIndices, mem_definableGraph_iff]

instance swapFirstTwoIndices_definable : ℒₛₑₜ-function₁[V] swapFirstTwoIndices := by
  unfold swapFirstTwoIndices
  definability

noncomputable def swapCode (L F n φ : V) : V :=
  renameCode L F (succ (succ n)) (succ (succ n)) (swapFirstTwoIndices n) φ

noncomputable def swapFragment (L F n : V) : V :=
  renamedFragment L F (succ (succ n)) (succ (succ n)) (swapFirstTwoIndices n)

instance swapCode_definable : ℒₛₑₜ-function₄[V] swapCode := by
  unfold swapCode renameCode
  apply Language.DefinableFunction₄.comp (by definability) (by definability) ?_ (by definability)
  exact Language.DefinableFunction₃.comp (by definability) (by definability) (by definability)

instance swapFragment_definable : ℒₛₑₜ-function₃[V] swapFragment := by
  unfold swapFragment renamedFragment
  apply Language.DefinableFunction₃.comp (by definability) (by definability) ?_
  exact Language.DefinableFunction₃.comp (by definability) (by definability) (by definability)

theorem swapFragment_valid {L F n : V} (hF : IsFragment L F) (hn : n ∈ (ω : V)) :
    IsFragment L (swapFragment L F n) :=
  renamedFragment_valid hF (ω_succ_closed (ω_succ_closed hn))
    (ω_succ_closed (ω_succ_closed hn)) (swapFirstTwoIndices_mem hn)

theorem swapFragment_countable {L F n : V} (hF : IsInternallyCountable F) :
    IsInternallyCountable (swapFragment L F n) := renamedFragment_countable hF

theorem swapCode_mem {L F n φ : V} (hφ : ⟨succ (succ n), φ⟩ₖ ∈ F) :
    ⟨succ (succ n), swapCode L F n φ⟩ₖ ∈ swapFragment L F n := renameCode_mem hφ

theorem holds_swapCode {L F M n φ b x y : V} (hF : IsFragment L F) (hM : IsStructureCode L M)
    (hn : n ∈ (ω : V)) (hφ : ⟨succ (succ n), φ⟩ₖ ∈ F)
    (hb : b ∈ structureDomain M ^ n) (hx : x ∈ structureDomain M) (hy : y ∈ structureDomain M) :
    Holds L (swapFragment L F n) M (succ (succ n)) (swapCode L F n φ)
      (assignmentPrepend (succ n) (assignmentPrepend n b x) y) ↔
    Holds L F M (succ (succ n)) φ (assignmentPrepend (succ n) (assignmentPrepend n b y) x) := by
  have h := holds_renameCode hF hM (ω_succ_closed (ω_succ_closed hn))
    (ω_succ_closed (ω_succ_closed hn)) (swapFirstTwoIndices_mem hn) hφ
    (assignmentPrepend_mem_function (ω_succ_closed hn) (assignmentPrepend_mem_function hn hb hx) hy)
  rw [compose_swapFirstTwo hn hb hx hy] at h
  exact h

theorem holds_swapCode_in_fragment {L F H M n φ b x y : V}
    (hF : IsFragment L F) (hH : IsFragment L H) (hM : IsStructureCode L M)
    (hn : n ∈ (ω : V)) (hφ : ⟨succ (succ n), φ⟩ₖ ∈ F)
    (hψ : ⟨succ (succ n), swapCode L F n φ⟩ₖ ∈ H)
    (hb : b ∈ structureDomain M ^ n) (hx : x ∈ structureDomain M) (hy : y ∈ structureDomain M) :
    Holds L H M (succ (succ n)) (swapCode L F n φ)
      (assignmentPrepend (succ n) (assignmentPrepend n b x) y) ↔
    Holds L F M (succ (succ n)) φ (assignmentPrepend (succ n) (assignmentPrepend n b y) x) :=
  (holds_fragment_iff hH (swapFragment_valid hF hn) _ _ hψ (swapCode_mem hφ) _).trans
    (holds_swapCode hF hM hn hφ hb hx hy)

end ZFVP.Infinitary.Internal
