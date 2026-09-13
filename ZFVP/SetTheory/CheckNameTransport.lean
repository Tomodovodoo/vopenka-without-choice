import ZFVP.SetTheory.CheckNames
import ZFVP.SetTheory.EndExtensionReplacement
import ZFVP.SetTheory.EndExtensionRelations
import ZFVP.SetTheory.EndExtensionCoding
import ZFVP.SetTheory.NameValue
import ZFVP.ModelTheory.ForcingModelChecks

/-! Membership end extensions commute with check names: `j (x̌) = (j x)̌` with respect to `j one`.
Hence the value of a checked check name under any filter containing the checked top is the
checked set. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem isMembershipRecursion_restrict {C C' : V} (hC' : IsTransitive C') (hsub : C' ⊆ C)
    {F : V → V → V} {f : V} (hf : IsMembershipRecursion C F f) :
    IsMembershipRecursion C' F (f ↾ C') := by
  have : IsFunction f := hf.1
  refine ⟨IsFunction.restrict f C', ?_, fun x hx ↦ ?_⟩
  · rw [domain_restrict_eq, hf.2.1]
    apply mem_ext
    intro z
    rw [mem_inter_iff]
    exact ⟨fun h ↦ h.2, fun h ↦ ⟨hsub z h, h⟩⟩
  · have hxdom : x ∈ domain f := by rw [hf.2.1]; exact hsub x hx
    rw [value_restrict hxdom hx, hf.2.2 x (hsub x hx), restrict_restrict_of_subset (hC'.transitive x hx)]

section

variable {W : Type*} [SetStructure W] [Nonempty W] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace MembershipEndExtension

variable (j : MembershipEndExtension V W)

omit [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [Nonempty W] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
theorem map_transitive {T : V} (hT : IsTransitive T) : IsTransitive (j T) := by
  refine ⟨fun y hy z hz ↦ ?_⟩
  obtain ⟨b, hb, rfl⟩ := j.endExtension T y hy
  obtain ⟨c, hc, rfl⟩ := j.endExtension b z hz
  exact (j.mem_iff _ _).mpr (hT.mem_trans hc hb)

theorem map_singleton (x : V) : j ({x} : V) = {j x} := by
  apply mem_ext
  intro z
  rw [mem_singleton_iff]
  constructor
  · intro hz
    obtain ⟨y, hy, rfl⟩ := j.endExtension _ z hz
    rw [mem_singleton_iff] at hy
    rw [hy]
  · rintro rfl
    exact (j.mem_iff _ _).mpr (mem_singleton_iff.mpr rfl)

theorem map_checkNameStep (one x g : V) (hg : IsFunction g) (hx : x ⊆ domain g) :
    j (checkNameStep one x g) = checkNameStep (j one) (j x) (j g) := by
  unfold checkNameStep
  rw [j.map_repl x (fun y ↦ ⟨g ‘ y, one⟩ₖ) (fun y ↦ ⟨(j g) ‘ y, j one⟩ₖ) (by definability) (by definability)]
  intro y hy
  rw [j.map_kpair, j.map_value g y (hx y hy)]

theorem map_checkName (one x : V) : j (checkName one x) = checkName (j one) (j x) := by
  obtain ⟨f, hf, hfx⟩ := (checkName_eq_iff one x (checkName one x)).mp rfl
  have hfun : IsFunction f := hf.1
  have hCtr : IsTransitive (transitiveClosure ({x} : V)) := transitiveClosure_transitive _
  have hxC : x ∈ transitiveClosure ({x} : V) :=
    ((transitiveClosure_characterization ({x} : V) _).mp rfl).2.1 x (mem_singleton_iff.mpr rfl)
  have hjf : IsMembershipRecursion (j (transitiveClosure ({x} : V))) (checkNameStep (j one)) (j f) := by
    refine ⟨j.map_function f, by rw [← j.map_domain, hf.2.1], ?_⟩
    intro y hy
    obtain ⟨y₀, hy₀, rfl⟩ := j.endExtension _ y hy
    have hy₀dom : y₀ ∈ domain f := by rw [hf.2.1]; exact hy₀
    rw [← j.map_value f y₀ hy₀dom, hf.2.2 y₀ hy₀, ← j.map_restrict]
    apply j.map_checkNameStep one y₀ (f ↾ y₀) (IsFunction.restrict f y₀)
    intro z hz
    rw [domain_restrict_eq, mem_inter_iff]
    exact ⟨by rw [hf.2.1]; exact hCtr.transitive y₀ hy₀ z hz, hz⟩
  have hjxC : j x ∈ j (transitiveClosure ({x} : V)) := (j.mem_iff _ _).mpr hxC
  have hsub : transitiveClosure ({j x} : W) ⊆ j (transitiveClosure ({x} : V)) := by
    apply transitiveClosure_minimal
    · intro z hz
      rw [mem_singleton_iff] at hz
      rw [hz]
      exact hjxC
    · exact j.map_transitive hCtr
  have hrec : IsMembershipRecursion (transitiveClosure ({j x} : W)) (checkNameStep (j one))
      ((j f) ↾ (transitiveClosure ({j x} : W))) :=
    isMembershipRecursion_restrict (transitiveClosure_transitive _) hsub hjf
  have htable := (membershipRecursionTable_eq_iff (checkNameStep (j one)) (by definability) (j x) _).mpr hrec
  have hjxC' : j x ∈ transitiveClosure ({j x} : W) :=
    ((transitiveClosure_characterization ({j x} : W) _).mp rfl).2.1 (j x) (mem_singleton_iff.mpr rfl)
  have hjxdom : j x ∈ domain (j f) := by rw [← j.map_domain, hf.2.1]; exact hjxC
  have : IsFunction (j f) := j.map_function f
  calc j (checkName one x) = j (f ‘ x) := by rw [hfx]
    _ = (j f) ‘ (j x) := j.map_value f x (by rw [hf.2.1]; exact hxC)
    _ = ((j f) ↾ (transitiveClosure ({j x} : W))) ‘ (j x) := (value_restrict hjxdom hjxC').symm
    _ = checkName (j one) (j x) := by
      show _ = (membershipRecursionTable (checkNameStep (j one)) _ (j x)) ‘ (j x)
      rw [← htable]

end MembershipEndExtension

end

namespace ForcingContext

variable (S : ForcingContext V)

theorem check_checkName (one x : V) : S.check (checkName one x) = checkName (S.check one) (S.check x) :=
  S.checkEmbedding.map_checkName one x

theorem nameValue_check_checkName {one : V} {H : S.Model} (hone : S.check one ∈ H) (x : V) :
    nameValue H (S.check (checkName one x)) = S.check x := by
  rw [S.check_checkName, nameValue_checkName hone]

end ForcingContext

end ZFVP
