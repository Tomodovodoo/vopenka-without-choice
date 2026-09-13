import ZFVP.Syntax.StandardTuples
import ZFVP.SetTheory.InfiniteDependentChoice

/-! External finite lists represented by internal sets and sequence graphs. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def standardListSet : List V → V
  | [] => ∅
  | x :: xs => insert x (standardListSet xs)

@[simp] theorem mem_standardListSet (xs : List V) (x : V) :
    x ∈ standardListSet xs ↔ x ∈ xs := by
  induction xs with
  | nil => simp [standardListSet]
  | cons y ys ih => simp [standardListSet, ih]

theorem standardListSet_mono {xs ys : List V} (h : xs ⊆ ys) :
    standardListSet xs ⊆ standardListSet ys := by
  intro x hx
  exact (mem_standardListSet ys x).mpr (h ((mem_standardListSet xs x).mp hx))

@[simp] theorem standardListSet_append (xs ys : List V) :
    standardListSet (xs ++ ys) = standardListSet xs ∪ standardListSet ys := by
  apply mem_ext
  intro x
  simp

noncomputable def standardList (xs : List V) : V := standardTuple xs.get

instance standardList_isFunction (xs : List V) : IsFunction (standardList xs) :=
  standardTuple_isFunction _

@[simp] theorem domain_standardList (xs : List V) : domain (standardList xs) = (xs.length : V) :=
  domain_standardTuple _

@[simp] theorem value_standardList (xs : List V) (i : Fin xs.length) :
    (standardList xs) ‘ (i.val : V) = xs.get i := value_standardTuple _ i

theorem mem_range_standardList (xs : List V) (x : V) :
    x ∈ range (standardList xs) ↔ x ∈ xs := by
  rw [mem_range_iff]
  constructor
  · rintro ⟨i, hi⟩
    obtain ⟨j, he⟩ := (mem_standardTuple_iff xs.get _).mp hi
    obtain ⟨_, hx⟩ := kpair_iff.mp he
    rw [hx]
    exact List.get_mem _ _
  · intro hx
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hx
    exact ⟨(i.val : V), (mem_standardTuple_iff xs.get _).mpr ⟨i, rfl⟩⟩

theorem range_standardList (xs : List V) : range (standardList xs) = standardListSet xs := by
  apply mem_ext
  intro x
  rw [mem_range_standardList, mem_standardListSet]

theorem range_restrict_standardList (xs : List V) (i : ℕ) :
    range ((standardList xs) ↾ (i : V)) = standardListSet (xs.take i) := by
  apply mem_ext
  intro x
  rw [mem_range_iff, mem_standardListSet]
  constructor
  · rintro ⟨j, hj⟩
    obtain ⟨hpair, hji⟩ := kpair_mem_restrict_iff.mp hj
    obtain ⟨k, hk⟩ := (mem_standardTuple_iff xs.get _).mp hpair
    obtain ⟨rfl, rfl⟩ := kpair_iff.mp hk
    have hki : k.val < i := (natCast_mem_iff _ _).mp hji
    exact List.mem_take_iff_getElem.mpr ⟨k.val, lt_min hki k.isLt, rfl⟩
  · intro hx
    obtain ⟨j, hj, rfl⟩ := List.mem_take_iff_getElem.mp hx
    refine ⟨(j : V), kpair_mem_restrict_iff.mpr ⟨?_, natCast_mem_of_lt (lt_min_iff.mp hj).1⟩⟩
    exact (mem_standardTuple_iff xs.get _).mpr ⟨⟨j, (lt_min_iff.mp hj).2⟩, rfl⟩

theorem standardList_injective {xs : List V} (hx : xs.Nodup) : Injective (standardList xs) := by
  intro i j x hi hj
  obtain ⟨k, hk⟩ := (mem_standardTuple_iff xs.get _).mp hi
  obtain ⟨l, hl⟩ := (mem_standardTuple_iff xs.get _).mp hj
  obtain ⟨rfl, hki⟩ := kpair_iff.mp hk
  obtain ⟨rfl, hlj⟩ := kpair_iff.mp hl
  have he : k = l := hx.injective_get (hki.symm.trans hlj)
  exact congrArg (fun t : Fin xs.length ↦ (t.val : V)) he

theorem standardListSet_internallyFinite (xs : List V) : IsInternallyFinite (standardListSet xs) := by
  classical
  let ys := xs.dedup
  have hy : ys.Nodup := List.nodup_dedup xs
  have he : range (standardList ys) = standardListSet xs := by
    apply mem_ext
    intro x
    simp [mem_range_standardList, ys]
  have hf := IsFunction.mem_function (standardList ys)
  rw [domain_standardList, he] at hf
  have hi := standardList_injective hy
  have hback := converseGraph_mem_function hf hi
  rw [he] at hback
  exact ⟨(ys.length : V), by simp,
    ⟨⟨converseGraph (standardList ys), hback, converseGraph_injective _⟩,
      ⟨standardList ys, hf, hi⟩⟩⟩

end ZFVP
