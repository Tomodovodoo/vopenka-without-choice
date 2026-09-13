import ZFVP.Syntax.TermBoundShift
import ZFVP.Syntax.Assignments

/-! Lift replacement tables across one binder, avoiding capture of their variables. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def liftBoundReplacement (L Δ m n B : V) : V :=
  assignmentPrepend n (compose B (termBoundShift L Δ m)) (boundVarCode 0)

noncomputable def liftFreeReplacement (L Δ m E : V) : V := compose E (termBoundShift L Δ m)

instance liftBoundReplacement_definable :
    Language.DefinableFunction₅ ℒₛₑₜ (liftBoundReplacement (V := V)) := by
  unfold liftBoundReplacement
  definability

instance liftFreeReplacement_definable : ℒₛₑₜ-function₄[V] liftFreeReplacement := by
  unfold liftFreeReplacement
  definability

theorem liftBoundReplacement_mem {L Δ m n B : V} (hL : IsLanguageCode L)
    (hm : m ∈ (ω : V)) (hn : n ∈ (ω : V)) (hB : B ∈ termSet L Δ m ^ n) :
    liftBoundReplacement L Δ m n B ∈ termSet L Δ (succ m) ^ succ n := by
  apply assignmentPrepend_mem_function hn
  · exact compose_function hB (termBoundShift_mem_function hL hm Δ)
  · exact (termSet_closed hL (ω_succ_closed hm) Δ).1 _ (zero_mem_succ_natural hm)

theorem liftFreeReplacement_mem {L Γ Δ m E : V} (hL : IsLanguageCode L)
    (hm : m ∈ (ω : V)) (hE : E ∈ termSet L Δ m ^ Γ) :
    liftFreeReplacement L Δ m E ∈ termSet L Δ (succ m) ^ Γ :=
  compose_function hE (termBoundShift_mem_function hL hm Δ)

theorem liftBoundReplacement_zero {n : V} (hn : n ∈ (ω : V)) (L Δ m B : V) :
    (liftBoundReplacement L Δ m n B) ‘ (0 : V) = boundVarCode 0 :=
  assignmentPrepend_zero hn _ _

theorem liftBoundReplacement_succ {L Δ m n B i : V}
    (hL : IsLanguageCode L) (hm : m ∈ (ω : V))
    (hn : n ∈ (ω : V)) (hB : B ∈ termSet L Δ m ^ n) (hi : i ∈ n) :
    (liftBoundReplacement L Δ m n B) ‘ (succ i) = (termBoundShift L Δ m) ‘ (B ‘ i) := by
  rw [liftBoundReplacement, assignmentPrepend_succ hn hi]
  exact value_compose_of_mem_function hB (termBoundShift_mem_function hL hm Δ) hi

theorem liftFreeReplacement_value {L Γ Δ m E x : V}
    (hL : IsLanguageCode L) (hm : m ∈ (ω : V))
    (hE : E ∈ termSet L Δ m ^ Γ) (hx : x ∈ Γ) :
    (liftFreeReplacement L Δ m E) ‘ x = (termBoundShift L Δ m) ‘ (E ‘ x) :=
  value_compose_of_mem_function hE (termBoundShift_mem_function hL hm Δ) hx

end ZFVP
