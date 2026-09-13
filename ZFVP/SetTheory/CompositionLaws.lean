import ZFVP.SetTheory.FunctionComposition

/-! Composition of internal relation graphs. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem graph_compose_assoc (f g h : V) : compose (compose f g) h = compose f (compose g h) := by
  apply mem_ext
  intro p
  constructor
  · rintro hp
    obtain ⟨x, z, w, hxz, hzw, rfl⟩ := mem_compose_iff.mp hp
    obtain ⟨y, hxy, hyz⟩ := kpair_mem_compose_iff.mp hxz
    exact mem_compose_iff.mpr ⟨x, y, w, hxy, kpair_mem_compose_iff.mpr ⟨z, hyz, hzw⟩, rfl⟩
  · rintro hp
    obtain ⟨x, y, w, hxy, hyw, rfl⟩ := mem_compose_iff.mp hp
    obtain ⟨z, hyz, hzw⟩ := kpair_mem_compose_iff.mp hyw
    exact mem_compose_iff.mpr ⟨x, z, w, kpair_mem_compose_iff.mpr ⟨y, hxy, hyz⟩, hzw, rfl⟩

theorem graph_compose_identity {f X Y : V} (hf : f ∈ Y ^ X) : compose f (identity Y) = f := by
  apply mem_ext
  intro p
  constructor
  · intro hp
    obtain ⟨x, y, z, hxy, hyz, rfl⟩ := mem_compose_iff.mp hp
    obtain ⟨_, rfl⟩ := kpair_mem_identity_iff.mp hyz
    exact hxy
  · intro hp
    obtain ⟨x, hx, y, hy, rfl⟩ := mem_prod_iff.mp (subset_prod_of_mem_function hf p hp)
    exact mem_compose_iff.mpr ⟨x, y, y, hp, kpair_mem_identity_iff.mpr ⟨hy, rfl⟩, rfl⟩

theorem graph_identity_compose {f X Y : V} (hf : f ∈ Y ^ X) : compose (identity X) f = f := by
  apply mem_ext
  intro p
  constructor
  · intro hp
    obtain ⟨x, y, z, hxy, hyz, rfl⟩ := mem_compose_iff.mp hp
    obtain ⟨_, rfl⟩ := kpair_mem_identity_iff.mp hxy
    exact hyz
  · intro hp
    obtain ⟨x, hx, y, hy, rfl⟩ := mem_prod_iff.mp (subset_prod_of_mem_function hf p hp)
    exact mem_compose_iff.mpr ⟨x, x, y, kpair_mem_identity_iff.mpr ⟨hx, rfl⟩, hp, rfl⟩

@[simp] theorem graph_empty_compose (f : V) : compose ∅ f = ∅ := by
  apply mem_ext
  intro p
  simp [mem_compose_iff]

theorem graph_compose_restrict {b A n : V} (hb : b ∈ A ^ n) (f : V) :
    compose b (f ↾ A) = compose b f := by
  apply mem_ext
  intro p
  constructor
  · intro hp
    obtain ⟨i, x, y, hib, hxf, rfl⟩ := mem_compose_iff.mp hp
    exact mem_compose_iff.mpr ⟨i, x, y, hib, (kpair_mem_restrict_iff.mp hxf).1, rfl⟩
  · intro hp
    obtain ⟨i, x, y, hib, hxf, rfl⟩ := mem_compose_iff.mp hp
    exact mem_compose_iff.mpr ⟨i, x, y, hib,
      kpair_mem_restrict_iff.mpr ⟨hxf, (mem_of_mem_functions hb hib).2⟩, rfl⟩

end ZFVP
