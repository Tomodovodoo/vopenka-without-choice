import ZFVP.ModelTheory.GroundRealsHOD
import ZFVP.SetTheory.OrdinalDefinabilityClosure

/-! The two descriptions of the full Solovay model agree in one direction: a set of the extension
that is definable from ground sets, reals and ordinals is ordinal definable over the extension
from the parameter class given by a formula `Pf` that holds of all ground sets and all reals.
Hereditary definability from those parameters gives hereditary ordinal definability. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace ForcingContext

/-- A Solovay parameter is an allowed parameter for the class defined by `Pf`, provided `Pf` holds
of every ground set and of every real of the extension. Ordinals are allowed outright. -/
theorem isAllowed_of_isSolovayParameter (A : ForcingContext V) (Pf : SetTheorySemisentence 2)
    {p : A.Model} (hPf_check : ∀ a : V, Pf.Evalb ![A.check a, p])
    (hPf_real : ∀ c : A.Model, c ⊆ A.check (ω : V) → Pf.Evalb ![c, p])
    {x : A.Model} (hx : A.IsSolovayParameter x) : IsAllowed Pf x p := by
  rcases hx with ⟨a, rfl⟩ | hreal | hord
  · exact Or.inr (Or.inr (hPf_check a))
  · exact Or.inr (Or.inr (hPf_real x hreal))
  · exact Or.inl hord

/-- A set of the extension defined from Solovay parameters is ordinal definable from the class. -/
theorem isOD_of_groundRealDefinable (A : ForcingContext V) (Pf : SetTheorySemisentence 2)
    {p : A.Model} (hPf_check : ∀ a : V, Pf.Evalb ![A.check a, p])
    (hPf_real : ∀ c : A.Model, c ⊆ A.check (ω : V) → Pf.Evalb ![c, p])
    {x : A.Model} (hx : A.IsGroundRealDefinable x) : IsOD Pf x p := by
  obtain ⟨n, φ, v, hv, hdef⟩ := hx
  exact isOD_of_definable_cons Pf φ
    (fun i ↦ isOD_of_allowed Pf
      (isAllowed_of_isSolovayParameter A Pf hPf_check hPf_real (hv i))) hdef

/-- Hereditary definability from Solovay parameters gives hereditary ordinal definability. -/
theorem isHOD_of_hereditarilyGroundRealDefinable (A : ForcingContext V)
    (Pf : SetTheorySemisentence 2) {p : A.Model}
    (hPf_check : ∀ a : V, Pf.Evalb ![A.check a, p])
    (hPf_real : ∀ c : A.Model, c ⊆ A.check (ω : V) → Pf.Evalb ![c, p])
    {x : A.Model} (hx : A.IsHereditarilyGroundRealDefinable x) : IsHOD Pf x p := by
  have hsub : transitiveClosure x ⊆ transitiveClosure ({x} : A.Model) :=
    transitiveClosure_minimal x _
      (fun w hw ↦ (transitiveClosure_transitive ({x} : A.Model)).mem_trans hw
        (self_mem_transitiveClosure_singleton x))
      (transitiveClosure_transitive _)
  refine ⟨isOD_of_groundRealDefinable A Pf hPf_check hPf_real
      (groundRealDefinable_of_hereditarily hx), fun y hy ↦ ?_⟩
  exact isOD_of_groundRealDefinable A Pf hPf_check hPf_real (hx y (hsub y hy))

end ForcingContext

end ZFVP
