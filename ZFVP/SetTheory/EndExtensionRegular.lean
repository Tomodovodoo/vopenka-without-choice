import ZFVP.SetTheory.EndExtensionAtomicForcing
import ZFVP.SetTheory.RegularSetAlgebra

/-! Regular sets, closures and joins are absolute for membership end extensions. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V W : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
  [SetStructure W] [Nonempty W] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace MembershipEndExtension

theorem map_forcingClosure (j : MembershipEndExtension V W) (P R A : V) :
    j (forcingClosure P R A) = forcingClosure (j P) (j R) (j A) := by
  unfold forcingClosure
  apply j.map_separation
  intro p hp
  rw [j.forall_mem_iff]
  apply forall_congr'
  intro q
  apply imp_congr_right
  intro hq
  rw [← j.map_kpair, j.mem_iff]
  apply imp_congr_right
  intro _
  constructor
  · rintro ⟨r, hr, hrq⟩
    exact ⟨j r, (j.mem_iff _ _).mpr hr, by rw [← j.map_kpair, j.mem_iff]; exact hrq⟩
  · rintro ⟨r, hr, hrq⟩
    obtain ⟨r₀, hr₀, rfl⟩ := j.endExtension A r hr
    rw [← j.map_kpair, j.mem_iff] at hrq
    exact ⟨r₀, hr₀, hrq⟩

theorem map_regularJoin (j : MembershipEndExtension V W) (P R X : V) :
    j (regularJoin P R X) = regularJoin (j P) (j R) (j X) := by
  unfold regularJoin
  rw [j.map_forcingClosure, j.map_sUnion]

theorem map_forcingRegular (j : MembershipEndExtension V W) {P R A : V} (hA : IsForcingRegular P R A) :
    IsForcingRegular (j P) (j R) (j A) := by
  refine ⟨(j.subset_iff _ _).mpr hA.1, ?_, ?_⟩
  · intro p hp q hq hqp
    obtain ⟨p₀, hp₀, rfl⟩ := j.endExtension A p hp
    obtain ⟨q₀, hq₀, rfl⟩ := j.endExtension P q hq
    rw [← j.map_kpair, j.mem_iff] at hqp
    exact (j.mem_iff _ _).mpr (hA.2.1 p₀ hp₀ q₀ hq₀ hqp)
  · intro p hp hd
    obtain ⟨p₀, hp₀, rfl⟩ := j.endExtension P p hp
    apply (j.mem_iff _ _).mpr
    apply hA.2.2 p₀ hp₀
    intro q₀ hq₀ hqp
    obtain ⟨r, hr, hrq⟩ := hd (j q₀) ((j.mem_iff _ _).mpr hq₀) (by rw [← j.map_kpair, j.mem_iff]; exact hqp)
    obtain ⟨r₀, hr₀, rfl⟩ := j.endExtension A r hr
    rw [← j.map_kpair, j.mem_iff] at hrq
    exact ⟨r₀, hr₀, hrq⟩

theorem map_inter (j : MembershipEndExtension V W) (x y : V) : j (x ∩ y) = j x ∩ j y := by
  apply mem_ext
  intro z
  rw [mem_inter_iff]
  constructor
  · intro hz
    obtain ⟨z₀, hz₀, rfl⟩ := j.endExtension _ z hz
    obtain ⟨h1, h2⟩ := mem_inter_iff.mp hz₀
    exact ⟨(j.mem_iff _ _).mpr h1, (j.mem_iff _ _).mpr h2⟩
  · rintro ⟨h1, h2⟩
    obtain ⟨z₀, hz₀, rfl⟩ := j.endExtension _ z h1
    rw [j.mem_iff] at h2
    exact (j.mem_iff _ _).mpr (mem_inter_iff.mpr ⟨hz₀, h2⟩)

theorem map_insert (j : MembershipEndExtension V W) (x y : V) : j (insert x y) = insert (j x) (j y) := by
  apply mem_ext
  intro z
  rw [mem_insert]
  constructor
  · intro hz
    obtain ⟨z₀, hz₀, rfl⟩ := j.endExtension _ z hz
    rcases mem_insert.mp hz₀ with rfl | h
    · exact Or.inl rfl
    · exact Or.inr ((j.mem_iff _ _).mpr h)
  · rintro (rfl | h)
    · exact (j.mem_iff _ _).mpr (mem_insert.mpr (Or.inl rfl))
    · obtain ⟨z₀, hz₀, rfl⟩ := j.endExtension _ z h
      exact (j.mem_iff _ _).mpr (mem_insert.mpr (Or.inr hz₀))

end MembershipEndExtension

end ZFVP
