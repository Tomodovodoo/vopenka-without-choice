import ZFVP.SetTheory.RealTranslations

/-! Rational translation acts on internal sets and preserves real open sets. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def realTranslateImageFormula : SetTheorySemisentence 3 :=
  f“B r A. ∀ y, y ∈ B ↔ ∃ x ∈ A, y = !realTranslateFormula r x”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def realTranslateImage (r A : V) : V :=
  repl (realTranslate r) (by definability) A

theorem mem_realTranslateImage_iff (r A y : V) :
    y ∈ realTranslateImage r A ↔ ∃ x ∈ A, realTranslate r x = y := by
  simp [realTranslateImage, repl_spec, eq_comm]

instance realTranslateImageFormula_defined :
    ℒₛₑₜ-function₂[V] realTranslateImage via realTranslateImageFormula :=
  ⟨fun v ↦ by simp [realTranslateImageFormula, mem_ext_iff (y := realTranslateImage _ _),
    mem_realTranslateImage_iff, eq_comm]⟩

instance realTranslateImage_definable : ℒₛₑₜ-function₂[V] realTranslateImage :=
  realTranslateImageFormula_defined.to_definable

theorem realTranslateImage_subset_reals (r : InternalRational V) {A : V}
    (hA : A ⊆ dedekindReals V) : realTranslateImage r.val A ⊆ dedekindReals V := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := (mem_realTranslateImage_iff _ _ _).mp hy
  exact (mem_dedekindReals_iff _).mpr
    (realTranslate_isCut r ((mem_dedekindReals_iff _).mp (hA x hx)))

theorem realTranslateImage_mem_iff (r : InternalRational V) {A x : V}
    (hA : A ⊆ dedekindReals V) (hx : IsDedekindCut x) :
    realTranslate r.val x ∈ realTranslateImage r.val A ↔ x ∈ A := by
  constructor
  · intro h
    obtain ⟨y, hy, he⟩ := (mem_realTranslateImage_iff _ _ _).mp h
    have hycut := (mem_dedekindReals_iff _).mp (hA y hy)
    exact ((realTranslate_eq_iff r hycut.1 hx.1).mp he) ▸ hy
  · intro h
    exact (mem_realTranslateImage_iff _ _ _).mpr ⟨x, h, rfl⟩

theorem realTranslateImage_inverse (r : InternalRational V) {A : V}
    (hA : A ⊆ dedekindReals V) :
    realTranslateImage (-r).val (realTranslateImage r.val A) = A := by
  apply mem_ext
  intro x
  constructor
  · intro h
    obtain ⟨y, hy, he⟩ := (mem_realTranslateImage_iff _ _ _).mp h
    obtain ⟨z, hz, rfl⟩ := (mem_realTranslateImage_iff _ _ _).mp hy
    rw [realTranslate_inverse r ((mem_dedekindReals_iff _).mp (hA z hz)).1] at he
    exact he ▸ hz
  · intro hx
    exact (mem_realTranslateImage_iff _ _ _).mpr ⟨realTranslate r.val x,
      (mem_realTranslateImage_iff _ _ _).mpr ⟨x, hx, rfl⟩,
      realTranslate_inverse r ((mem_dedekindReals_iff _).mp (hA x hx)).1⟩

theorem realTranslateImage_interval (r a b : InternalRational V) :
    realTranslateImage r.val (realInterval a.val b.val) =
      realInterval (a + r).val (b + r).val := by
  apply mem_ext
  intro y
  constructor
  · intro h
    obtain ⟨x, hx, rfl⟩ := (mem_realTranslateImage_iff _ _ _).mp h
    exact (realTranslate_interval_iff r a b ((mem_realInterval_iff _ _ _).mp hx).1).mpr hx
  · intro hy
    have hycut := ((mem_realInterval_iff _ _ _).mp hy).1
    have hxcut := realTranslate_isCut (-r) hycut
    have he : realTranslate r.val (realTranslate (-r).val y) = y := by
      simpa using realTranslate_inverse (-r) hycut.1
    refine (mem_realTranslateImage_iff _ _ _).mpr ⟨realTranslate (-r).val y, ?_, he⟩
    apply (realTranslate_interval_iff r a b hxcut).mp
    simpa only [he] using hy

theorem realTranslateImage_isOpen (r : InternalRational V) {U : V}
    (hU : IsRealOpen U) : IsRealOpen (realTranslateImage r.val U) := by
  apply realOpen_of_neighborhoods
  intro y hy
  obtain ⟨x, hx, rfl⟩ := (mem_realTranslateImage_iff _ _ _).mp hy
  obtain ⟨a, ha, b, hb, hab, hxi, hiU⟩ := realOpen_neighborhood hU hx
  let p : InternalRational V := ⟨a, ha⟩
  let q : InternalRational V := ⟨b, hb⟩
  refine ⟨(p + r).val, (p + r).property, (q + r).val, (q + r).property,
    show p + r < q + r from by
      simpa only [add_comm] using (add_lt_add_right (show p < q from hab) r), ?_, ?_⟩
  · exact (realTranslate_interval_iff r p q ((mem_realInterval_iff _ _ _).mp hxi).1).mpr hxi
  · intro z hz
    rw [← realTranslateImage_interval r p q] at hz
    obtain ⟨w, hw, rfl⟩ := (mem_realTranslateImage_iff _ _ _).mp hz
    exact (mem_realTranslateImage_iff _ _ _).mpr ⟨w, hiU w hw, rfl⟩

theorem realTranslateImage_complement (r : InternalRational V) {A : V}
    (hA : A ⊆ dedekindReals V) :
    realTranslateImage r.val ((dedekindReals V) \ A) =
      (dedekindReals V) \ realTranslateImage r.val A := by
  apply mem_ext
  intro y
  constructor
  · intro h
    obtain ⟨x, hx, rfl⟩ := (mem_realTranslateImage_iff _ _ _).mp h
    obtain ⟨hxR, hxA⟩ := mem_sdiff_iff.mp hx
    have hxcut := (mem_dedekindReals_iff _).mp hxR
    exact mem_sdiff_iff.mpr ⟨(mem_dedekindReals_iff _).mpr (realTranslate_isCut r hxcut),
      fun hm ↦ hxA ((realTranslateImage_mem_iff r hA hxcut).mp hm)⟩
  · intro h
    obtain ⟨hyR, hyA⟩ := mem_sdiff_iff.mp h
    have hycut := (mem_dedekindReals_iff _).mp hyR
    have hxcut := realTranslate_isCut (-r) hycut
    have he : realTranslate r.val (realTranslate (-r).val y) = y := by
      simpa using realTranslate_inverse (-r) hycut.1
    refine (mem_realTranslateImage_iff _ _ _).mpr ⟨realTranslate (-r).val y,
      mem_sdiff_iff.mpr ⟨(mem_dedekindReals_iff _).mpr hxcut, ?_⟩, he⟩
    intro hxA
    exact hyA ((mem_realTranslateImage_iff _ _ _).mpr ⟨_, hxA, he⟩)

theorem realTranslateImage_closed (r : InternalRational V) {A : V}
    (hA : A ⊆ dedekindReals V) (hclosed : IsRealOpen ((dedekindReals V) \ A)) :
    IsRealOpen ((dedekindReals V) \ realTranslateImage r.val A) := by
  rw [← realTranslateImage_complement r hA]
  exact realTranslateImage_isOpen r hclosed

end ZFVP
