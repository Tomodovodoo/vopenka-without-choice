import ZFVP.SetTheory.WellFoundedAttempts

/-! Internal well-founded recursion, proved using Collection of partial solutions. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem recursionAttempt_extend {R D : V} {F : V → V → V} {f x : V}
    (hf : IsRecursionAttempt R D F f) (hxD : x ∈ D) (hx : x ∉ domain f)
    (hpred : predecessors R D x ⊆ domain f) :
    IsRecursionAttempt R D F (insert ⟨x, F x (f ↾ (predecessors R D x))⟩ₖ f) := by
  have : IsFunction f := hf.1
  let v := F x (f ↾ (predecessors R D x))
  have hnew : IsFunction (insert ⟨x, v⟩ₖ f) := IsFunction.insert f x v hx
  change IsRecursionAttempt R D F (insert ⟨x, v⟩ₖ f)
  refine ⟨hnew, ⟨?_, ?_⟩, ?_⟩
  · intro y hy
    rcases show y = x ∨ y ∈ domain f from by simpa using hy with heq | hy
    · subst y
      exact hxD
    · exact hf.2.1.1 y hy
  · intro y hy z hz
    rcases show y = x ∨ y ∈ domain f from by simpa using hy with heq | hy
    · subst y
      have hm := hpred z hz
      simpa using Or.inr hm
    · have hm := hf.2.1.2 y hy z hz
      simpa using Or.inr hm
  · intro y hy
    rcases show y = x ∨ y ∈ domain f from by simpa using hy with heq | hy
    · subst y
      have hxp : x ∉ predecessors R D x := fun h ↦ hx (hpred x h)
      rw [value_eq_of_kpair_mem (f := insert ⟨x, v⟩ₖ f) (x := x) (y := v) (by simp),
        restrict_insert_kpair_eq_restrict_of_not_mem hxp]
    · have hxp : x ∉ predecessors R D y := fun h ↦ hx (hf.2.1.2 y hy x h)
      have hv : (insert ⟨x, v⟩ₖ f) ‘ y = f ‘ y :=
        value_eq_of_kpair_mem (mem_insert.mpr (Or.inr (kpair_value_mem hy)))
      rw [hv, restrict_insert_kpair_eq_restrict_of_not_mem hxp]
      exact hf.2.2 y hy

theorem recursionAttempt_exists_at {R D : V} (hR : IsInternallyWellFounded R D)
    (F : V → V → V) (hF : ℒₛₑₜ-function₂ F) :
    ∀ x ∈ D, ∃ f, IsRecursionAttempt R D F f ∧ x ∈ domain f := by
  have hdef := isRecursionAttempt_definable R D F hF
  apply internalWellFounded_induction hR
    (fun x ↦ ∃ f, IsRecursionAttempt R D F f ∧ x ∈ domain f) (by definability)
  intro x hx ih
  obtain ⟨B, hcover, hmembers⟩ := strongCollection (predecessors R D x)
    (fun y f ↦ IsRecursionAttempt R D F f ∧ y ∈ domain f) (by definability) (by
      intro y hy
      obtain ⟨hyD, hyx⟩ := (mem_predecessors_iff R D x y).mp hy
      exact ih y hyD hyx)
  have hB : ∀ f ∈ B, IsRecursionAttempt R D F f := by
    intro f hf
    obtain ⟨y, _, hfy, _⟩ := hmembers f hf
    exact hfy
  have hU := recursionAttempt_sUnion hR hB
  have hp : predecessors R D x ⊆ domain (⋃ˢ B) := by
    intro y hy
    obtain ⟨f, hf, _, hyf⟩ := hcover y hy
    exact (mem_domain_sUnion_iff B y).mpr ⟨f, hf, hyf⟩
  by_cases hxU : x ∈ domain (⋃ˢ B)
  · exact ⟨⋃ˢ B, hU, hxU⟩
  · exact ⟨insert ⟨x, F x ((⋃ˢ B) ↾ (predecessors R D x))⟩ₖ (⋃ˢ B),
      recursionAttempt_extend hU hx hxU hp, by simp⟩

theorem wellFoundedRecursion_existsUnique {R D : V} (hR : IsInternallyWellFounded R D)
    (F : V → V → V) (hF : ℒₛₑₜ-function₂ F) :
    ∃! f, IsRecursionAttempt R D F f ∧ domain f = D := by
  have hdef := isRecursionAttempt_definable R D F hF
  obtain ⟨B, hcover, hmembers⟩ := strongCollection D
    (fun x f ↦ IsRecursionAttempt R D F f ∧ x ∈ domain f) (by definability)
    (recursionAttempt_exists_at hR F hF)
  have hB : ∀ f ∈ B, IsRecursionAttempt R D F f := by
    intro f hf
    obtain ⟨x, _, hfx, _⟩ := hmembers f hf
    exact hfx
  have hU := recursionAttempt_sUnion hR hB
  have hd : domain (⋃ˢ B) = D := by
    apply SetTheory.subset_antisymm hU.2.1.1
    intro x hx
    obtain ⟨f, hf, _, hxf⟩ := hcover x hx
    exact (mem_domain_sUnion_iff B x).mpr ⟨f, hf, hxf⟩
  refine ⟨⋃ˢ B, ⟨hU, hd⟩, ?_⟩
  rintro g ⟨hg, hgd⟩
  have : IsFunction g := hg.1
  have : IsFunction (⋃ˢ B) := hU.1
  apply functions_eq_of_domain_values (hgd.trans hd.symm)
  intro x hx
  exact recursionAttempt_values_coherent hR hg hU x hx (by simpa only [hd, hgd] using hx)

noncomputable def wellFoundedRecursion {R D : V} (hR : IsInternallyWellFounded R D)
    (F : V → V → V) (hF : ℒₛₑₜ-function₂ F) : V :=
  Classical.choose! (wellFoundedRecursion_existsUnique hR F hF)

theorem wellFoundedRecursion_spec {R D : V} (hR : IsInternallyWellFounded R D)
    (F : V → V → V) (hF : ℒₛₑₜ-function₂ F) :
    IsRecursionAttempt R D F (wellFoundedRecursion hR F hF) ∧
      domain (wellFoundedRecursion hR F hF) = D :=
  Classical.choose!_spec (wellFoundedRecursion_existsUnique hR F hF)

instance wellFoundedRecursion_isFunction {R D : V} (hR : IsInternallyWellFounded R D)
    (F : V → V → V) (hF : ℒₛₑₜ-function₂ F) :
    IsFunction (wellFoundedRecursion hR F hF) :=
  (wellFoundedRecursion_spec hR F hF).1.1

@[simp] theorem domain_wellFoundedRecursion {R D : V} (hR : IsInternallyWellFounded R D)
    (F : V → V → V) (hF : ℒₛₑₜ-function₂ F) :
    domain (wellFoundedRecursion hR F hF) = D :=
  (wellFoundedRecursion_spec hR F hF).2

theorem wellFoundedRecursion_value {R D : V} (hR : IsInternallyWellFounded R D)
    (F : V → V → V) (hF : ℒₛₑₜ-function₂ F) {x : V} (hx : x ∈ D) :
    (wellFoundedRecursion hR F hF) ‘ x =
      F x ((wellFoundedRecursion hR F hF) ↾ (predecessors R D x)) :=
  (wellFoundedRecursion_spec hR F hF).1.2.2 x (by simpa using hx)

theorem wellFoundedRecursion_eq_iff {R D : V} (hR : IsInternallyWellFounded R D)
    (F : V → V → V) (hF : ℒₛₑₜ-function₂ F) (f : V) :
    wellFoundedRecursion hR F hF = f ↔ IsRecursionAttempt R D F f ∧ domain f = D := by
  constructor
  · rintro rfl
    exact wellFoundedRecursion_spec hR F hF
  · intro hf
    exact (wellFoundedRecursion_existsUnique hR F hF).unique
      (wellFoundedRecursion_spec hR F hF) hf

end ZFVP

