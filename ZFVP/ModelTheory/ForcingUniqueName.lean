import ZFVP.SetTheory.ForcingUniqueName
import ZFVP.ModelTheory.ForcingModel

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace ForcingContext
variable (A : ForcingContext V) (F : V → V → V) (hF : ℒₛₑₜ-function₂ F) (a : V)

/-- Under uniqueness, every bounded witness represents the same object;
Collection guarantees that any witnessed object has a bounded representative. -/
theorem mem_witnessName_iff (Q : A.Model → Prop)
    (ht : ∀ ν : ForcingName A.P, GenericMeets A.G (F a ν.val) ↔ Q (A.ofName ν))
    (hu : ∀ x y, Q x → Q y → x = y) (x : A.Model) :
    x ∈ A.ofName ⟨forcingWitnessName A.P F hF a, forcingWitnessName_isName A.P F hF a⟩ ↔ Q x := by
  rw [A.mem_ofName_iff]
  constructor
  · rintro ⟨ν, p, hpG, hp, rfl⟩
    exact (ht ν).mp ⟨p, hpG, ((mem_forcingWitnessName_iff A.P F hF a ν.val p).mp hp).2.2.2⟩
  · intro hx
    obtain ⟨ν, rfl⟩ := A.ofName_surjective x
    obtain ⟨p, hpG, hpF⟩ := (ht ν).mpr hx
    obtain ⟨μ, hμB, hμN, hpμ⟩ := forcingWitnessBound_spec A.P F hF a p
      (A.generic.1.1 p hpG) ⟨ν.val, ν.property, hpF⟩
    let μ' : ForcingName A.P := ⟨μ, hμN⟩
    exact ⟨μ', p, hpG, (mem_forcingWitnessName_iff A.P F hF a μ p).mpr
      ⟨hμB, A.generic.1.1 p hpG, hμN, hpμ⟩,
      hu _ _ hx ((ht μ').mp ⟨p, hpG, hpμ⟩)⟩

theorem uniqueName_value (Q : A.Model → Prop)
    (ht : ∀ ν : ForcingName A.P, GenericMeets A.G (F a ν.val) ↔ Q (A.ofName ν))
    (hu : ∀ x y, Q x → Q y → x = y) {x : A.Model} (hx : Q x) :
    A.ofName ⟨forcingUniqueName A.P A.R F hF a, forcingUniqueName_isName A.P A.R F hF a⟩ = x := by
  apply mem_ext
  intro z
  have he := forcingQuotient_unionName A.P A.R A.G A.order A.generic
    ⟨forcingWitnessName A.P F hF a, forcingWitnessName_isName A.P F hF a⟩ z
  change z ∈ A.ofName ⟨forcingUniqueName A.P A.R F hF a, _⟩ ↔
    ∃ y : A.Model, y ∈ A.ofName ⟨forcingWitnessName A.P F hF a, _⟩ ∧ z ∈ y at he
  rw [he]
  constructor
  · rintro ⟨y, hy, hzy⟩
    have hyx := hu y x ((A.mem_witnessName_iff F hF a Q ht hu y).mp hy) hx
    exact hyx ▸ hzy
  · intro hz
    exact ⟨x, (A.mem_witnessName_iff F hF a Q ht hu x).mpr hx, hz⟩

end ForcingContext
end ZFVP
