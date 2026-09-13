import ZFVP.SetTheory.EndExtensionRelations
import ZFVP.Syntax.StandardTuples

/-! Quantifier assignments agree under ZF membership end extensions. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

namespace MembershipEndExtension

variable {V W : Type*} [SetStructure V] [SetStructure W]
  [Nonempty V] [Nonempty W] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem map_prependValue (j : MembershipEndExtension V W) (b x i : V) :
    j (prependValue b x i) = prependValue (j b) (j x) (j i) := by
  have hzero : j (0 : V) = (0 : W) := j.map_numeral 0
  have hz : j i = (0 : W) ↔ i = (0 : V) := by rw [← hzero, j.injective.eq_iff]
  unfold prependValue
  split_ifs <;> (try simp only [j.map_value_total, j.map_sUnion])
  all_goals tauto

theorem map_assignmentPrepend (j : MembershipEndExtension V W) (n b x : V) :
    j (assignmentPrepend n b x) = assignmentPrepend (j n) (j b) (j x) := by
  have he := j.map_definableGraph (succ n) (prependValue b x) (prependValue (j b) (j x))
    (by definability) (by definability) (fun i _ ↦ j.map_prependValue b x i)
  simpa only [assignmentPrepend, j.map_succ] using he

theorem map_standardTuple (j : MembershipEndExtension V W) {n : ℕ} (v : Fin n → V) :
    j (standardTuple v) = standardTuple (j ∘ v) := by
  induction n with
  | zero => exact j.map_empty
  | succ n ih =>
    simp only [standardTuple, j.map_assignmentPrepend, j.map_numeral, ih, Function.comp_def]

end MembershipEndExtension
end ZFVP
