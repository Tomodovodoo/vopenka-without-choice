import ZFVP.ModelTheory.SymmetricModel
import ZFVP.SetTheory.SymmetricUnionName

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace SymmetricContext

theorem check_empty (S : SymmetricContext V) (x : S.Model) : x ∉ S.check ∅ := by
  intro hx
  obtain ⟨y, hy, _⟩ := (S.mem_check_iff ∅ x).mp hx
  exact not_mem_empty hy

theorem empty_set (S : SymmetricContext V) : ∃ e : S.Model, ∀ x, x ∉ e :=
  ⟨S.check ∅, S.check_empty⟩

noncomputable def pairName (S : SymmetricContext V) (σ τ : S.Name) : S.Name :=
  ⟨{⟨σ.val, S.one⟩ₖ, ⟨τ.val, S.one⟩ₖ},
    hereditarilySymmetric_pair S.poset S.group S.normal S.top σ.property τ.property⟩

theorem mem_pairName_iff (S : SymmetricContext V) (σ τ : S.Name) (x : S.Model) :
    x ∈ S.ofName (S.pairName σ τ) ↔ x = S.ofName σ ∨ x = S.ofName τ := by
  have hh := forcingQuotient_pairName S.P S.R S.G S.order S.generic
    ⟨σ.val, σ.property.1⟩ ⟨τ.val, τ.property.1⟩ S.one
    (externalForcingFilter_top S.generic.1 S.top) (S.toOrdinary x)
  exact hh.trans (or_congr (S.toOrdinary_injective.eq_iff (a := x) (b := S.ofName σ))
    (S.toOrdinary_injective.eq_iff (a := x) (b := S.ofName τ)))

theorem pairing (S : SymmetricContext V) (x y : S.Model) :
    ∃ z : S.Model, ∀ w, w ∈ z ↔ w = x ∨ w = y := by
  obtain ⟨σ, rfl⟩ := S.ofName_surjective x
  obtain ⟨τ, rfl⟩ := S.ofName_surjective y
  exact ⟨S.ofName (S.pairName σ τ), S.mem_pairName_iff σ τ⟩

noncomputable def unionName (S : SymmetricContext V) (τ : S.Name) : S.Name :=
  ⟨forcingUnionName S.P S.R τ.val, hereditarilySymmetric_forcingUnionName S.group S.normal τ.property⟩

theorem mem_unionName_iff (S : SymmetricContext V) (τ : S.Name) (x : S.Model) :
    x ∈ S.ofName (S.unionName τ) ↔ ∃ y : S.Model, y ∈ S.ofName τ ∧ x ∈ y := by
  have hh := forcingQuotient_unionName S.P S.R S.G S.order S.generic
    ⟨τ.val, τ.property.1⟩ (S.toOrdinary x)
  constructor
  · intro hx
    obtain ⟨y, hy, hxy⟩ := hh.mp hx
    obtain ⟨z, hz, rfl⟩ := S.inclusion.endExtension (S.ofName τ) y hy
    exact ⟨z, hz, hxy⟩
  · rintro ⟨y, hy, hxy⟩
    exact hh.mpr ⟨S.toOrdinary y, hy, hxy⟩

theorem union_set (S : SymmetricContext V) (x : S.Model) :
    ∃ z : S.Model, ∀ w, w ∈ z ↔ ∃ y, y ∈ x ∧ w ∈ y := by
  obtain ⟨τ, rfl⟩ := S.ofName_surjective x
  exact ⟨S.ofName (S.unionName τ), S.mem_unionName_iff τ⟩

theorem check_succ (S : SymmetricContext V) (a : V) (x : S.Model) :
    x ∈ S.check (succ a) ↔ x = S.check a ∨ x ∈ S.check a := by
  have hh := forcingCheck_succ S.P S.R S.G S.order S.generic S.one S.top a (S.toOrdinary x)
  exact hh.trans (or_congr (S.toOrdinary_injective.eq_iff (a := x) (b := S.check a)) Iff.rfl)

theorem infinity (S : SymmetricContext V) : ∃ I : S.Model,
    (∀ e, (∀ z, z ∉ e) → e ∈ I) ∧
      (∀ x, x ∈ I → ∀ y, (∀ z, z ∈ y ↔ z = x ∨ z ∈ x) → y ∈ I) := by
  refine ⟨S.check ω, ?_, ?_⟩
  · intro e he
    have heq : e = S.check ∅ := S.extensionality e (S.check ∅)
      (fun z ↦ iff_of_false (he z) (S.check_empty z))
    rw [heq]
    exact (S.check_mem_iff ∅ ω).mpr empty_mem_ω
  · intro x hx y hy
    obtain ⟨a, ha, rfl⟩ := (S.mem_check_iff ω x).mp hx
    have heq : y = S.check (succ a) := S.extensionality y (S.check (succ a))
      (fun z ↦ (hy z).trans (S.check_succ a z).symm)
    rw [heq]
    exact (S.check_mem_iff (succ a) ω).mpr (ω_succ_closed ha)

end SymmetricContext
end ZFVP
