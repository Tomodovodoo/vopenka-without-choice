import ZFVP.Syntax.FoundationSubstitution
import ZFVP.SetTheory.NaturalPredecessor

/-! Bound-variable shifting, the first component of substitution under binders. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def boundShiftReplacement (n : V) : V :=
  definableGraph n (fun i ↦ boundVarCode (succ i)) (by definability)

noncomputable def freeIdentityReplacement (Γ : V) : V :=
  definableGraph Γ freeVarCode (by definability)

theorem boundShiftReplacement_value {n i : V} (hi : i ∈ n) :
    (boundShiftReplacement n) ‘ i = boundVarCode (succ i) := value_definableGraph _ _ _ hi

theorem freeIdentityReplacement_value {Γ x : V} (hx : x ∈ Γ) :
    (freeIdentityReplacement Γ) ‘ x = freeVarCode x := value_definableGraph _ _ _ hx

instance boundShiftReplacement_definable : ℒₛₑₜ-function₁[V] boundShiftReplacement := by
  have h : ℒₛₑₜ-relation (fun B n : V ↦ ∀ p, p ∈ B ↔ ∃ i ∈ n, p = ⟨i, boundVarCode (succ i)⟩ₖ) := by
    definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = boundShiftReplacement (v 1) ↔ _
  rw [mem_ext_iff]
  simp only [boundShiftReplacement, mem_definableGraph_iff]

instance freeIdentityReplacement_definable : ℒₛₑₜ-function₁[V] freeIdentityReplacement := by
  have h : ℒₛₑₜ-relation (fun E Γ : V ↦ ∀ p, p ∈ E ↔ ∃ x ∈ Γ, p = ⟨x, freeVarCode x⟩ₖ) := by
    definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = freeIdentityReplacement (v 1) ↔ _
  rw [mem_ext_iff]
  simp only [freeIdentityReplacement, mem_definableGraph_iff]

theorem boundShiftReplacement_mem {L n : V} (hL : IsLanguageCode L)
    (hn : n ∈ (ω : V)) (Γ : V) : boundShiftReplacement n ∈ termSet L Γ (succ n) ^ n := by
  apply definableGraph_mem_function_of_mapsTo
  intro i hi
  exact (termSet_closed hL (ω_succ_closed hn) Γ).1 _ (succ_mem_succ_of_natural_mem hn hi)

theorem freeIdentityReplacement_mem {L n : V} (hL : IsLanguageCode L)
    (hn : n ∈ (ω : V)) (Γ : V) : freeIdentityReplacement Γ ∈ termSet L Γ n ^ Γ := by
  apply definableGraph_mem_function_of_mapsTo
  intro x hx
  exact (termSet_closed hL hn Γ).2.1 x hx

noncomputable def termBoundShift (L Γ n : V) : V :=
  termSubstitution L Γ n (boundShiftReplacement n) (freeIdentityReplacement Γ)

instance termBoundShift_definable : ℒₛₑₜ-function₃[V] termBoundShift := by
  unfold termBoundShift
  exact Language.DefinableFunction₅.comp (by definability) (by definability) (by definability)
    (by definability) (by definability)

instance termBoundShift_isFunction (L Γ n : V) : IsFunction (termBoundShift L Γ n) :=
  termSubstitution_isFunction _ _ _ _ _

@[simp] theorem domain_termBoundShift (L Γ n : V) : domain (termBoundShift L Γ n) = termSet L Γ n :=
  domain_termSubstitution _ _ _ _ _

theorem termBoundShift_mem_function {L n : V} (hL : IsLanguageCode L) (hn : n ∈ (ω : V)) (Γ : V) :
    termBoundShift L Γ n ∈ termSet L Γ (succ n) ^ termSet L Γ n :=
  termSubstitution_mem_function hL hn (ω_succ_closed hn)
    (boundShiftReplacement_mem hL hn Γ) (freeIdentityReplacement_mem hL (ω_succ_closed hn) Γ)

theorem termBoundShift_value_mem {L n t : V} (hL : IsLanguageCode L) (hn : n ∈ (ω : V))
    (Γ : V) (ht : t ∈ termSet L Γ n) :
    (termBoundShift L Γ n) ‘ t ∈ termSet L Γ (succ n) :=
  function_value_mem (termBoundShift_mem_function hL hn Γ) ht

theorem termBoundShift_boundVar {L n i : V} (hL : IsLanguageCode L) (hn : n ∈ (ω : V))
    (Γ : V) (hi : i ∈ n) : (termBoundShift L Γ n) ‘ (boundVarCode i) = boundVarCode (succ i) := by
  rw [termBoundShift, termSubstitution_boundVar hL hn _ _ _ hi, boundShiftReplacement_value hi]

theorem termBoundShift_freeVar {L n x : V} (hL : IsLanguageCode L) (hn : n ∈ (ω : V))
    (Γ : V) (hx : x ∈ Γ) : (termBoundShift L Γ n) ‘ (freeVarCode x) = freeVarCode x := by
  rw [termBoundShift, termSubstitution_freeVar hL hn _ _ _ hx, freeIdentityReplacement_value hx]

theorem encodeSemiterm_bShift {Λ : Language} {ξ : Type*} {L Γ : V}
    (hL : IsLanguageCode L) (F : ∀ {k}, Λ.Func k → V) (e : ξ → V)
    (hF : ∀ k (f : Λ.Func k), F f ∈ functionSymbols L ∧
      (functionArities L) ‘ (F f) = (k : V)) (he : ∀ x, e x ∈ Γ)
    {n : ℕ} (t : Semiterm Λ ξ n) :
    (termBoundShift L Γ (n : V)) ‘ (encodeSemiterm F e t) =
      encodeSemiterm F e (Rew.bShift t) := by
  apply encodeSemiterm_rew hL F e e hF he Rew.bShift
  · intro i
    rw [boundShiftReplacement_value (natCast_mem_of_lt i.isLt)]
    simp only [Rew.bShift_bvar, encodeSemiterm, Fin.val_succ, num_succ_def]
  · intro x
    rw [freeIdentityReplacement_value (he x)]
    rfl

end ZFVP
