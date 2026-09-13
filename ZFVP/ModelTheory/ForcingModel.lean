import ZFVP.ModelTheory.ForcingQuotientZF
import ZFVP.SetTheory.MembershipEndExtension

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable (V : Type*) [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- The ground forcing data, with an external generic filter. -/
structure ForcingContext where
  P : V
  R : V
  one : V
  G : Set V
  order : IsForcingPreorder P R
  top : IsForcingTop P R one
  generic : IsExternalForcingGeneric P R G

variable {V}

namespace ForcingContext

def Model (S : ForcingContext V) := ForcingQuotient S.P S.R S.G S.order S.generic.1

instance modelSetStructure (S : ForcingContext V) : SetStructure S.Model :=
  inferInstanceAs (SetStructure (ForcingQuotient S.P S.R S.G S.order S.generic.1))

instance modelNonempty (S : ForcingContext V) : Nonempty S.Model :=
  inferInstanceAs (Nonempty (ForcingQuotient S.P S.R S.G S.order S.generic.1))

instance modelZF (S : ForcingContext V) : S.Model↓[ℒₛₑₜ] ⊧* 𝗭𝗙 :=
  forcingQuotient_models_zf S.P S.R S.G S.order S.generic S.one S.top

noncomputable def ofName (S : ForcingContext V) (τ : ForcingName S.P) : S.Model :=
  forcingQuotientMk S.P S.R S.G S.order S.generic.1 τ

theorem ofName_surjective (S : ForcingContext V) : Function.Surjective S.ofName :=
  forcingQuotientMk_surjective S.P S.R S.G S.order S.generic.1

theorem mem_ofName_iff (S : ForcingContext V) (τ : ForcingName S.P) (x : S.Model) :
    x ∈ S.ofName τ ↔ ∃ ν : ForcingName S.P, ∃ p ∈ S.G, ⟨ν.val, p⟩ₖ ∈ τ.val ∧ x = S.ofName ν := by
  obtain ⟨σ, rfl⟩ := S.ofName_surjective x
  exact forcingQuotientMk_mem_subname_iff S.P S.R S.G S.order S.generic σ τ

noncomputable def check (S : ForcingContext V) (x : V) : S.Model :=
  forcingCheck S.P S.R S.G S.order S.generic.1 S.one S.top x

theorem check_eq_iff (S : ForcingContext V) (x y : V) : S.check x = S.check y ↔ x = y :=
  forcingCheck_eq_iff S.P S.R S.G S.order S.generic.1 S.one S.top x y

theorem check_mem_iff (S : ForcingContext V) (x y : V) : S.check x ∈ S.check y ↔ x ∈ y :=
  forcingCheck_mem_iff S.P S.R S.G S.order S.generic.1 S.one S.top x y

theorem mem_check_iff (S : ForcingContext V) (a : V) (x : S.Model) :
    x ∈ S.check a ↔ ∃ y ∈ a, x = S.check y :=
  forcingCheck_endExtension S.P S.R S.G S.order S.generic S.one S.top a x

noncomputable def checkEmbedding (S : ForcingContext V) : MembershipEndExtension V S.Model where
  toFun := S.check
  injective := fun _ _ h ↦ (S.check_eq_iff _ _).mp h
  mem_iff := S.check_mem_iff
  endExtension := fun x y h ↦ (S.mem_check_iff x y).mp h

theorem check_bounded (S : ForcingContext V) {n : ℕ} {φ : SetTheorySemisentence n}
    (hφ : IsBoundedSetFormula φ) (b : Fin n → V) :
    φ.Evalb b ↔ φ.Evalb (fun i ↦ S.check (b i)) :=
  S.checkEmbedding.bounded_elementary hφ b

end ForcingContext
end ZFVP
