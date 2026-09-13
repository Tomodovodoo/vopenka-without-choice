import ZFVP.SetTheory.BoundedCodingPrimitives

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def boundedValueFormula : SetTheorySemisentence 3 :=
  “v f x. (∀ z ∈ v, ∃ p ∈ f, ∃ d ∈ p, ∃ y ∈ d, !boundedKpairFormula p x y ∧ z ∈ y) ∧
    ∀ p ∈ f, ∀ d ∈ p, ∀ y ∈ d, !boundedKpairFormula p x y → !isSubsetOf y v”

theorem boundedValueFormula_bounded : IsBoundedSetFormula boundedValueFormula := by
  repeat' first
    | exact boundedKpairFormula_bounded.subst _
    | exact (boundedKpairFormula_bounded.subst _).neg
    | exact isSubsetOf_bounded.subst _
    | exact IsBoundedSetFormula.rel _ _
    | apply IsBoundedSetFormula.all
    | apply IsBoundedSetFormula.exs
    | apply IsBoundedSetFormula.and
    | apply IsBoundedSetFormula.or

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem mem_value_iff_exists_pair (f x z : V) :
    z ∈ f ‘ x ↔ ∃ y, ⟨x, y⟩ₖ ∈ f ∧ z ∈ y := by
  change z ∈ {z ∈ ⋃ˢ range f ; ∃ y, z ∈ y ∧ ⟨x, y⟩ₖ ∈ f} ↔ _
  rw [mem_sep_iff]
  constructor
  · rintro ⟨_, y, hz, hp⟩
    exact ⟨y, hp, hz⟩
  · rintro ⟨y, hp, hz⟩
    exact ⟨mem_sUnion_iff.mpr ⟨y, mem_range_of_kpair_mem hp, hz⟩, y, hz, hp⟩

theorem eval_boundedValueFormula (v f x : V) :
    boundedValueFormula.Evalb ![v, f, x] ↔ v = f ‘ x := by
  have he : boundedValueFormula.Evalb ![v, f, x] ↔
      (∀ z ∈ v, ∃ p ∈ f, ∃ d ∈ p, ∃ y ∈ d, p = ⟨x, y⟩ₖ ∧ z ∈ y) ∧
      ∀ p ∈ f, ∀ d ∈ p, ∀ y ∈ d, p = ⟨x, y⟩ₖ → y ⊆ v := by
    simp [boundedValueFormula]
  rw [he]
  constructor
  · rintro ⟨hf, hb⟩
    apply mem_ext
    intro z
    rw [mem_value_iff_exists_pair]
    constructor
    · intro hz
      obtain ⟨p, hp, d, _, y, _, rfl, hzy⟩ := hf z hz
      exact ⟨y, hp, hzy⟩
    · rintro ⟨y, hp, hzy⟩
      exact hb ⟨x, y⟩ₖ hp (doubleton x y) (by simp [kpair, pair_eq_doubleton])
        y (by simp) rfl z hzy
  · rintro rfl
    constructor
    · intro z hz
      obtain ⟨y, hp, hzy⟩ := (mem_value_iff_exists_pair f x z).mp hz
      exact ⟨⟨x, y⟩ₖ, hp, doubleton x y, by simp [kpair, pair_eq_doubleton], y, by simp, rfl, hzy⟩
    · intro p hp d _ y _ hxy z hz
      exact (mem_value_iff_exists_pair f x z).mpr ⟨y, hxy ▸ hp, hz⟩

instance boundedValueFormula_defined : ℒₛₑₜ-function₂[V] value via boundedValueFormula := by
  refine ⟨fun v ↦ ?_⟩
  have hv : ![v 0, v 1, v 2] = v := by
    funext i
    exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun t ↦ Fin.cases rfl (fun e ↦ Fin.elim0 e) t) j) i
  change boundedValueFormula.Evalb v ↔ v 0 = (v 1) ‘ (v 2)
  rw [← hv]
  exact eval_boundedValueFormula _ _ _

end ZFVP

