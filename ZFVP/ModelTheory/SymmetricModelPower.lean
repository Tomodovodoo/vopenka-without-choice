import ZFVP.ModelTheory.SymmetricModelBoundedNames
import ZFVP.SetTheory.SymmetricPowerName

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace SymmetricContext

noncomputable def powerName (S : SymmetricContext V) (τ : S.Name) : S.Name :=
  ⟨symmetricPowerName S.P S.R S.Γ S.F τ.val,
    hereditarilySymmetric_symmetricPowerName S.order S.group S.normal τ.property⟩

theorem subsetConditions_truth (S : SymmetricContext V) (ρ τ : S.Name) :
    GenericMeets S.G (symmetricSubsetConditions S.P S.R S.Γ S.F ρ.val τ.val) ↔
      ∀ x : S.Model, x ∈ S.ofName ρ → x ∈ S.ofName τ := by
  have hh := (S.formula_truth isSubsetOf ![ρ, τ]).symm
  have ht : (fun i ↦ (![ρ, τ] i).val) = ![ρ.val, τ.val] := by
    funext i
    exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun k ↦ Fin.elim0 k) j) i
  rw [ht] at hh
  simpa [symmetricSubsetConditions, isSubsetOf, Semiformula.Evalb, Structure.rel] using hh

theorem mem_powerName_iff (S : SymmetricContext V) (τ : S.Name) (x : S.Model) :
    x ∈ S.ofName (S.powerName τ) ↔ ∀ z, z ∈ x → z ∈ S.ofName τ := by
  constructor
  · intro hx
    obtain ⟨ρ, p, hpG, hp, he⟩ := (S.mem_ofName_iff _ _).mp hx
    obtain ⟨_, _, _, hpF⟩ := (mem_symmetricPowerName_iff _ _ _ _ _ _ _).mp hp
    rw [he]
    exact (S.subsetConditions_truth ρ τ).mp ⟨p, hpG, hpF⟩
  · intro hx
    obtain ⟨ρ, hρ, rfl⟩ := S.boundedRepresentative τ x hx
    obtain ⟨p, hpG, hpF⟩ := (S.subsetConditions_truth ρ τ).mpr hx
    exact (S.mem_ofName_iff _ _).mpr
      ⟨ρ, p, hpG, (mem_symmetricPowerName_iff _ _ _ _ _ _ _).mpr
        ⟨hρ, S.generic.1.1 p hpG, ρ.property, hpF⟩, rfl⟩

theorem power_set (S : SymmetricContext V) (a : S.Model) :
    ∃ b : S.Model, ∀ x, x ∈ b ↔ ∀ z, z ∈ x → z ∈ a := by
  obtain ⟨τ, rfl⟩ := S.ofName_surjective a
  exact ⟨S.ofName (S.powerName τ), S.mem_powerName_iff τ⟩

end SymmetricContext
end ZFVP
