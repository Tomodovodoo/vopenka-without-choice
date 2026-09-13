import ZFVP.Syntax.MembershipTailTemplates
import ZFVP.Syntax.VopenkaAxiomSet

/-! Definability of the schema compiler with its parameter count as an input. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

attribute [local aesop 4 (rule_sets := [Definability]) safe] Language.DefinableFunction₄.comp

instance prependTuple_definable {m : ℕ} (v : Fin m → V) :
    ℒₛₑₜ-function₂[V] (fun n b ↦ prependTuple n b v) := by
  induction m with
  | zero => change ℒₛₑₜ-function₂[V] (fun _ b ↦ b); definability
  | succ m ih =>
    have := ih (fun i ↦ v i.succ)
    simp only [prependTuple]
    definability

instance prefixRenaming_definable {a m : ℕ} (r : Fin a → Fin m) :
    ℒₛₑₜ-function₁[V] (prefixRenaming r) := by
  change ℒₛₑₜ-function₁[V] (fun n ↦ prependTuple n (skipIndices m n) (fun i ↦ ((r i).val : V)))
  exact Language.DefinableFunction₂.comp (F := fun n b ↦ prependTuple n b (fun i ↦ ((r i).val : V)))
    (by definability) (by definability)

instance MembershipTemplate.compileTail_definable {a m : ℕ} (t : MembershipTemplate a m) :
    ℒₛₑₜ-function₂[V] (fun n φ ↦ t.compileTail n φ) := by
  induction t with
  | fixed ψ => simp only [MembershipTemplate.compileTail]; definability
  | hole r => simp only [MembershipTemplate.compileTail]; definability
  | conj s t ihs iht => simp only [MembershipTemplate.compileTail]; definability
  | disj s t ihs iht => simp only [MembershipTemplate.compileTail]; definability
  | neg s ih => simp only [MembershipTemplate.compileTail]; definability
  | all s ih => simp only [MembershipTemplate.compileTail]; definability
  | exs s ih => simp only [MembershipTemplate.compileTail]; definability

end ZFVP
