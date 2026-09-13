import ZFVP.ModelTheory.InternalJointNamedConjunction
import ZFVP.ModelTheory.FiniteJointNamingFormula
import ZFVP.Syntax.StandardOmegaMembershipSyntax

/-! The finite parameter and variable positions used to express internal
source and upper-name restrictions in first-order syntax. -/

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def finiteInternalSourceNames (D R j : V) (N : ℕ) (t : Fin N) :
    Option (BinaryRelationDomain D R) := by
  classical
  exact if h : ∃ x : BinaryRelationDomain D R, j ‘ x.val = (t.val : V)
    then some h.choose else none

theorem finiteInternalSourceNames_some_iff {D R j : V} (hj : j ∈ (ω : V) ^ D)
    (hji : Injective j) {N : ℕ} (t : Fin N) (x : BinaryRelationDomain D R) :
    finiteInternalSourceNames D R j N t = some x ↔ j ‘ x.val = (t.val : V) := by
  classical
  unfold finiteInternalSourceNames
  split
  · rename_i h
    constructor
    · intro he
      exact Option.some.inj he ▸ h.choose_spec
    · intro hx
      congr 1
      exact Subtype.ext (injective_value_eq hj hji h.choose.property x.property (h.choose_spec.trans hx.symm))
  · rename_i h
    exact ⟨(fun he ↦ by cases he), fun hx ↦ False.elim (h ⟨x, hx⟩)⟩

noncomputable def finiteInternalUpperSlots (k : V) {p : ℕ} (indices : Fin p → V)
    (N : ℕ) (t : Fin p) : Option (Fin N) := by
  classical
  exact if h : ∃ s : Fin N, k ‘ (indices t) = (s.val : V) then some h.choose else none

theorem finiteInternalUpperSlots_some_iff (k : V) {N p : ℕ} (indices : Fin p → V)
    (t : Fin p) (s : Fin N) :
    finiteInternalUpperSlots k indices N t = some s ↔ k ‘ (indices t) = (s.val : V) := by
  classical
  unfold finiteInternalUpperSlots
  split
  · rename_i h
    constructor
    · intro he
      exact Option.some.inj he ▸ h.choose_spec
    · intro hs
      congr 1
      exact Fin.ext (natCast_injective (h.choose_spec.symm.trans hs))
  · rename_i h
    exact ⟨(fun he ↦ by cases he), fun hs ↦ False.elim (h ⟨s, hs⟩)⟩

theorem finiteInternalSourceNames_constraints {D R j : V} (hj : j ∈ (ω : V) ^ D)
    (hji : Injective j) {N : ℕ} (a : Fin N → BinaryRelationDomain D R) :
    (∀ t x, finiteInternalSourceNames D R j N t = some x → a t = x) ↔
      ∀ x ∈ D, j ‘ x ∈ (N : V) → (standardTuple (fun t ↦ (a t).val)) ‘ (j ‘ x) = x := by
  constructor
  · intro h x hx hxn
    obtain ⟨t, ht⟩ := (mem_natCast_iff (j ‘ x) N).mp hxn
    have he := h t (⟨x, hx⟩ : BinaryRelationDomain D R)
      ((finiteInternalSourceNames_some_iff hj hji t ⟨x, hx⟩).mpr ht)
    rw [ht, value_standardTuple]
    exact congrArg Subtype.val he
  · intro h t x hs
    have ht := (finiteInternalSourceNames_some_iff hj hji t x).mp hs
    apply Subtype.ext
    have he := h x.val x.property (ht ▸ natCast_mem_of_lt t.isLt)
    rwa [ht, value_standardTuple] at he

theorem finiteInternalUpperSlots_constraints {D R I k c : V} {N p : ℕ}
    (indices : Fin p → V) (his : ∀ t, indices t ∈ I)
    (hcover : ∀ i ∈ I, k ‘ i ∈ (N : V) → ∃ t, indices t = i)
    (hc : c ∈ D ^ I) (a : Fin N → BinaryRelationDomain D R) :
    (∀ t s, finiteInternalUpperSlots k indices N t = some s →
      a s = (⟨c ‘ (indices t), function_value_mem hc (his t)⟩ : BinaryRelationDomain D R)) ↔
      ∀ i ∈ I, k ‘ i ∈ (N : V) → (standardTuple (fun t ↦ (a t).val)) ‘ (k ‘ i) = c ‘ i := by
  constructor
  · intro h i hi hin
    obtain ⟨t, rfl⟩ := hcover i hi hin
    obtain ⟨s, hs⟩ := (mem_natCast_iff (k ‘ (indices t)) N).mp hin
    have he := h t s ((finiteInternalUpperSlots_some_iff k indices t s).mpr hs)
    rw [hs, value_standardTuple]
    exact congrArg Subtype.val he
  · intro h t s hs
    have ht := (finiteInternalUpperSlots_some_iff k indices t s).mp hs
    apply Subtype.ext
    have he := h (indices t) (his t) (ht ▸ natCast_mem_of_lt s.isLt)
    rwa [ht, value_standardTuple] at he

end ZFVP
