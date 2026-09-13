import ZFVP.SetTheory.MembershipRecursion
import ZFVP.SetTheory.ForcingNames

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def checkNameStep (one x g : V) : V :=
  repl (fun y ↦ ⟨g ‘ y, one⟩ₖ) (by definability) x

instance checkNameStep_definable : ℒₛₑₜ-function₃[V] checkNameStep := by
  have h : ℒₛₑₜ-relation₄ (fun C one x g : V ↦ ∀ z, z ∈ C ↔ ∃ y ∈ x, z = ⟨g ‘ y, one⟩ₖ) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = checkNameStep (v 1) (v 2) (v 3) ↔ _
  rw [mem_ext_iff]
  simp [checkNameStep, repl_spec]

noncomputable def checkName (one x : V) : V :=
  membershipRecursion (checkNameStep one) (by definability) x

theorem checkName_eq_iff (one x y : V) : y = checkName one x ↔
    ∃ f, IsMembershipRecursion (transitiveClosure ({x} : V)) (checkNameStep one) f ∧ y = f ‘ x := by
  constructor
  · rintro rfl
    exact ⟨membershipRecursionTable (checkNameStep one) (by definability) x,
      membershipRecursionTable_spec _ _ _, rfl⟩
  · rintro ⟨f, hf, rfl⟩
    have he := (membershipRecursionTable_eq_iff (checkNameStep one) (by definability) x f).mpr hf
    exact congrArg (fun g ↦ g ‘ x) he

instance checkName_definable : ℒₛₑₜ-function₂[V] checkName := by
  have h : ℒₛₑₜ-relation₃ (fun y one x : V ↦
      ∃ f, IsMembershipRecursion (transitiveClosure ({x} : V)) (checkNameStep one) f ∧ y = f ‘ x) := by
    unfold IsMembershipRecursion
    definability
  apply Language.Definable.of_iff h
  intro v
  exact checkName_eq_iff (v 1) (v 2) (v 0)

theorem mem_checkName_iff (one x z : V) :
    z ∈ checkName one x ↔ ∃ y ∈ x, z = ⟨checkName one y, one⟩ₖ := by
  rw [checkName, membershipRecursion_equation]
  change z ∈ checkNameStep one x (definableGraph x (checkName one) (by definability)) ↔ _
  simp only [checkNameStep, repl_spec]
  constructor
  · rintro ⟨y, hy, he⟩
    exact ⟨y, hy, by simpa only [value_definableGraph _ _ _ hy] using he⟩
  · rintro ⟨y, hy, he⟩
    exact ⟨y, hy, by simpa only [value_definableGraph _ _ _ hy] using he⟩

theorem checkName_isName {P one : V} (hone : one ∈ P) (x : V) : IsForcingName P (checkName one x) := by
  apply set_induction (fun x ↦ IsForcingName P (checkName one x)) (by definability) ?_ x
  intro x ih
  apply (forcingName_iff _ _).mpr
  intro z hz
  obtain ⟨y, hy, rfl⟩ := (mem_checkName_iff one x z).mp hz
  exact ⟨checkName one y, one, hone, rfl, ih y hy⟩

theorem checkName_injective (one : V) : Function.Injective (checkName one) := by
  intro x
  apply set_induction (fun x ↦ ∀ y : V, checkName one x = checkName one y → x = y)
    (by definability) ?_ x
  intro x ih y he
  apply SetTheory.mem_ext_iff.mpr
  intro z
  constructor
  · intro hz
    have hmem : ⟨checkName one z, one⟩ₖ ∈ checkName one y :=
      he ▸ (mem_checkName_iff one x _).mpr ⟨z, hz, rfl⟩
    obtain ⟨w, hw, hzw⟩ := (mem_checkName_iff one y _).mp hmem
    have hezw := ih z hz w (kpair_iff.mp hzw).1
    exact hezw ▸ hw
  · intro hz
    have hmem : ⟨checkName one z, one⟩ₖ ∈ checkName one x :=
      he.symm ▸ (mem_checkName_iff one y _).mpr ⟨z, hz, rfl⟩
    obtain ⟨w, hw, hzw⟩ := (mem_checkName_iff one x _).mp hmem
    have hewz := ih w hw z (kpair_iff.mp hzw).1.symm
    exact hewz ▸ hw

theorem checkName_empty (one : V) : checkName one ∅ = ∅ := by
  apply SetTheory.mem_ext_iff.mpr
  intro z
  simp [mem_checkName_iff]

theorem checkName_pair (one x y : V) :
    checkName one ({x, y} : V) = ({⟨checkName one x, one⟩ₖ, ⟨checkName one y, one⟩ₖ} : V) := by
  apply SetTheory.mem_ext_iff.mpr
  intro z
  simp [mem_checkName_iff]

end ZFVP
