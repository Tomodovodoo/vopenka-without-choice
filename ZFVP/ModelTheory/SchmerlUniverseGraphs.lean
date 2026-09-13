import ZFVP.ModelTheory.SchmerlStandardOmega
import ZFVP.SetTheory.CountableSets
import Mathlib.Basic.Countable.Small

/-! External functions on a set-sized universe carrier have actual internal
graphs. For this standard universe, internal and external countability agree. -/

namespace ZFVP.Schmerl

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem HasStandardOmega.countable_omega (h : HasStandardOmega V) :
    Countable {n : V // n ∈ (ω : V)} := by
  apply Function.Surjective.countable (f := fun k : ℕ ↦ (⟨(k : V), by simp⟩ : {n : V // n ∈ (ω : V)}))
  intro n
  obtain ⟨k, hk⟩ := h n.val n.property
  exact ⟨k, Subtype.ext hk.symm⟩

theorem externalCountable_of_internal (hω : HasStandardOmega V) {A : V}
    (hA : IsInternallyCountable A) : Countable {x : V // x ∈ A} := by
  let := hω.countable_omega
  obtain ⟨f, hf, hi⟩ := hA
  let := IsFunction.of_mem hf
  let F : {x : V // x ∈ A} → {n : V // n ∈ (ω : V)} :=
    fun x ↦ ⟨f ‘ x.val, function_value_mem hf x.property⟩
  apply Function.Injective.countable (f := F)
  intro x y he
  have hv : f ‘ x.val = f ‘ y.val := congrArg Subtype.val he
  apply Subtype.ext
  apply hi x.val y.val (f ‘ x.val)
  · exact kpair_value_mem (by simpa only [domain_eq_of_mem_function hf] using x.property)
  · rw [hv]
    exact kpair_value_mem (by simpa only [domain_eq_of_mem_function hf] using y.property)

noncomputable def universeGraph (A : Universe.{u}) (f : {x : Universe.{u} // x ∈ A} → Universe.{u}) :
    Universe.{u} := Universe.mk (Set.range (fun x ↦ ⟨x.val, f x⟩ₖ))

theorem mem_universeGraph (A : Universe.{u}) (f : {x : Universe.{u} // x ∈ A} → Universe.{u})
    (p : Universe.{u}) : p ∈ universeGraph A f ↔ ∃ x, p = ⟨x.val, f x⟩ₖ := by
  simp only [universeGraph, Universe.mem_mk, Set.mem_range, eq_comm]

theorem pair_mem_universeGraph (A : Universe.{u}) (f : {x : Universe.{u} // x ∈ A} → Universe.{u})
    (x y : Universe.{u}) :
    ⟨x, y⟩ₖ ∈ universeGraph A f ↔ ∃ hx : x ∈ A, y = f ⟨x, hx⟩ := by
  rw [mem_universeGraph]
  constructor
  · rintro ⟨⟨z, hz⟩, he⟩
    obtain ⟨rfl, rfl⟩ := kpair_iff.mp he
    exact ⟨hz, rfl⟩
  · rintro ⟨hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩

theorem universeGraph_mem_function {A B : Universe.{u}}
    (f : {x : Universe.{u} // x ∈ A} → Universe.{u}) (hf : ∀ x, f x ∈ B) :
    universeGraph A f ∈ B ^ A := by
  apply mem_function_iff.mpr
  constructor
  · intro p hp
    obtain ⟨x, rfl⟩ := (mem_universeGraph A f p).mp hp
    exact kpair_mem_iff.mpr ⟨x.property, hf x⟩
  · intro x hx
    refine ⟨f ⟨x, hx⟩, (pair_mem_universeGraph A f x _).mpr ⟨hx, rfl⟩, ?_⟩
    intro y hy
    obtain ⟨_, he⟩ := (pair_mem_universeGraph A f x y).mp hy
    exact he

instance universeGraph_isFunction (A : Universe.{u})
    (f : {x : Universe.{u} // x ∈ A} → Universe.{u}) : IsFunction (universeGraph A f) :=
  IsFunction.of_mem (universeGraph_mem_function f (B := Universe.mk (Set.range f))
    (fun x ↦ Universe.mem_mk.mpr ⟨x, rfl⟩))

theorem domain_universeGraph (A : Universe.{u})
    (f : {x : Universe.{u} // x ∈ A} → Universe.{u}) : domain (universeGraph A f) = A :=
  domain_eq_of_mem_function (universeGraph_mem_function f (B := Universe.mk (Set.range f))
    (fun x ↦ Universe.mem_mk.mpr ⟨x, rfl⟩))

@[simp] theorem value_universeGraph (A : Universe.{u})
    (f : {x : Universe.{u} // x ∈ A} → Universe.{u}) (x : {x : Universe.{u} // x ∈ A}) :
    (universeGraph A f) ‘ x.val = f x :=
  value_eq_of_kpair_mem ((pair_mem_universeGraph A f x.val (f x)).mpr ⟨x.property, rfl⟩)

theorem universeGraph_injective {A : Universe.{u}}
    {f : {x : Universe.{u} // x ∈ A} → Universe.{u}} (hf : Function.Injective f) :
    Injective (universeGraph A f) := by
  intro x y z hx hy
  obtain ⟨hxA, hxz⟩ := (pair_mem_universeGraph A f x z).mp hx
  obtain ⟨hyA, hyz⟩ := (pair_mem_universeGraph A f y z).mp hy
  exact congrArg Subtype.val (hf (hxz.symm.trans hyz))

theorem internalCountable_of_external {A : Universe.{u}} (hA : Countable {x : Universe.{u} // x ∈ A}) :
    IsInternallyCountable A := by
  let := hA
  let e := @Encodable.encode {x : Universe.{u} // x ∈ A} (Encodable.ofCountable _)
  let f : {x : Universe.{u} // x ∈ A} → Universe.{u} := fun x ↦ (e x : Universe.{u})
  refine ⟨universeGraph A f, universeGraph_mem_function f (fun _ ↦ by simp [f]), ?_⟩
  apply universeGraph_injective
  intro x y hxy
  apply @Encodable.encode_injective {x : Universe.{u} // x ∈ A} (Encodable.ofCountable _)
  exact natCast_injective hxy

theorem universe_internalCountable_iff (A : Universe.{u}) :
    IsInternallyCountable A ↔ Countable {x : Universe.{u} // x ∈ A} :=
  ⟨externalCountable_of_internal universe_standardOmega, internalCountable_of_external⟩

noncomputable def universeNaturalIndex (n : {n : Universe.{u} // n ∈ (ω : Universe.{u})}) : ℕ :=
  Classical.choose (universe_standardOmega n.val n.property)

@[simp] theorem universeNaturalIndex_spec (n : {n : Universe.{u} // n ∈ (ω : Universe.{u})}) :
    (universeNaturalIndex n : Universe.{u}) = n.val :=
  (Classical.choose_spec (universe_standardOmega n.val n.property)).symm

@[simp] theorem universeNaturalIndex_numeral (n : ℕ) :
    universeNaturalIndex (⟨(n : Universe.{u}), by simp⟩) = n :=
  natCast_injective (universeNaturalIndex_spec _)

noncomputable def universeSequence (f : ℕ → Universe.{u}) : Universe.{u} :=
  universeGraph (ω : Universe.{u}) (fun n ↦ f (universeNaturalIndex n))

instance universeSequence_isFunction (f : ℕ → Universe.{u}) : IsFunction (universeSequence f) :=
  inferInstanceAs (IsFunction (universeGraph _ _))

@[simp] theorem domain_universeSequence (f : ℕ → Universe.{u}) :
    domain (universeSequence f) = (ω : Universe.{u}) := domain_universeGraph _ _

@[simp] theorem value_universeSequence (f : ℕ → Universe.{u}) (n : ℕ) :
    (universeSequence f) ‘ (n : Universe.{u}) = f n := by
  have he := value_universeGraph (ω : Universe.{u})
    (fun n ↦ f (universeNaturalIndex n)) ⟨(n : Universe.{u}), by simp⟩
  simpa only [universeSequence, universeNaturalIndex_numeral] using he

end ZFVP.Schmerl
