import ZFVP.ModelTheory.ForcingModel
import ZFVP.ModelTheory.ClassForcingQuotientClosed
import ZFVP.ModelTheory.ClassForcingQuotientTruth
import ZFVP.SetTheory.SymmetricFormulaForcing

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable (V : Type*) [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

structure SymmetricContext extends ForcingContext V where
  Γ : V
  F : V
  poset : IsForcingPoset P R
  group : IsForcingAutomorphismGroup P R Γ
  normal : IsNormalSubgroupFilter P Γ F

variable {V}

namespace SymmetricContext

abbrev Name (S : SymmetricContext V) := {τ : V // IsHereditarilySymmetricName S.P S.Γ S.F τ}

def Model (S : SymmetricContext V) :=
  ClassForcingQuotient S.P S.R S.G S.order S.generic.1 (IsHereditarilySymmetricName S.P S.Γ S.F)
    (fun _ h ↦ h.1)

instance modelSetStructure (S : SymmetricContext V) : SetStructure S.Model :=
  inferInstanceAs (SetStructure (ClassForcingQuotient S.P S.R S.G S.order S.generic.1 _ _))

def ofName (S : SymmetricContext V) (τ : S.Name) : S.Model :=
  ClassForcingQuotient.ofName S.P S.R S.G S.order S.generic.1 _ _ τ

theorem ofName_surjective (S : SymmetricContext V) : Function.Surjective S.ofName :=
  ClassForcingQuotient.ofName_surjective S.P S.R S.G S.order S.generic.1 _ _

noncomputable def check (S : SymmetricContext V) (x : V) : S.Model :=
  S.ofName ⟨ZFVP.checkName S.one x, hereditarilySymmetric_checkName S.poset S.group S.normal S.top x⟩

instance modelNonempty (S : SymmetricContext V) : Nonempty S.Model := ⟨S.check ∅⟩

def toOrdinary (S : SymmetricContext V) (x : S.Model) : S.toForcingContext.Model := x.val

theorem toOrdinary_ofName (S : SymmetricContext V) (τ : S.Name) :
    S.toOrdinary (S.ofName τ) = S.toForcingContext.ofName ⟨τ.val, τ.property.1⟩ := rfl

theorem toOrdinary_check (S : SymmetricContext V) (x : V) :
    S.toOrdinary (S.check x) = S.toForcingContext.check x := rfl

theorem toOrdinary_injective (S : SymmetricContext V) : Function.Injective S.toOrdinary :=
  fun _ _ h ↦ Subtype.ext h

theorem toOrdinary_mem_iff (S : SymmetricContext V) (x y : S.Model) :
    S.toOrdinary x ∈ S.toOrdinary y ↔ x ∈ y := Iff.rfl

def inclusion (S : SymmetricContext V) : MembershipEndExtension S.Model S.toForcingContext.Model :=
  ClassForcingQuotient.inclusion S.P S.R S.G S.order S.generic _ _
    (fun τ hτ σ p hp ↦ (hereditarilySymmetric_iff S.P S.Γ S.F τ).mp hτ |>.2 σ p hp)

theorem mem_ofName_iff (S : SymmetricContext V) (τ : S.Name) (x : S.Model) :
    x ∈ S.ofName τ ↔ ∃ σ : S.Name, ∃ p ∈ S.G, ⟨σ.val, p⟩ₖ ∈ τ.val ∧ x = S.ofName σ :=
  ClassForcingQuotient.mem_ofName_iff S.P S.R S.G S.order S.generic _ _
    (fun τ hτ σ p hp ↦ (hereditarilySymmetric_iff S.P S.Γ S.F τ).mp hτ |>.2 σ p hp) τ x

theorem extensionality (S : SymmetricContext V) (x y : S.Model)
    (he : ∀ z, z ∈ x ↔ z ∈ y) : x = y :=
  ClassForcingQuotient.extensionality S.P S.R S.G S.order S.generic _ _
    (fun τ hτ σ p hp ↦ (hereditarilySymmetric_iff S.P S.Γ S.F τ).mp hτ |>.2 σ p hp) x y he

theorem foundation (S : SymmetricContext V) (x : S.Model) (hx : ∃ y, y ∈ x) :
    ∃ y, y ∈ x ∧ ∀ z, z ∈ x → z ∉ y :=
  ClassForcingQuotient.foundation S.P S.R S.G S.order S.generic _ _
    (fun τ hτ σ p hp ↦ (hereditarilySymmetric_iff S.P S.Γ S.F τ).mp hτ |>.2 σ p hp) x hx

theorem ofName_cons (S : SymmetricContext V) {n : ℕ} (v : Fin n → S.Name) (σ : S.Name) :
    (fun i ↦ S.ofName ((σ :> v) i)) = (S.ofName σ :> fun i ↦ S.ofName (v i)) := by
  funext i
  exact Fin.cases rfl (fun _ ↦ rfl) i

theorem formula_truth (S : SymmetricContext V) {n : ℕ} (φ : SetTheorySemisentence n)
    (v : Fin n → S.Name) :
    φ.Evalb (fun i ↦ S.ofName (v i)) ↔
      GenericMeets S.G (symmetricForcingFormula S.P S.R S.Γ S.F φ (standardTuple (fun i ↦ (v i).val))) :=
  ClassForcingQuotient.formula_truth S.P S.R S.G S.order S.generic _ (by definability) _ φ v

theorem check_eq_iff (S : SymmetricContext V) (x y : V) : S.check x = S.check y ↔ x = y := by
  rw [← S.toOrdinary_injective.eq_iff, toOrdinary_check, toOrdinary_check]
  exact S.toForcingContext.check_eq_iff x y

theorem check_mem_iff (S : SymmetricContext V) (x y : V) : S.check x ∈ S.check y ↔ x ∈ y := by
  rw [← toOrdinary_mem_iff, toOrdinary_check, toOrdinary_check]
  exact S.toForcingContext.check_mem_iff x y

theorem mem_check_iff (S : SymmetricContext V) (a : V) (x : S.Model) :
    x ∈ S.check a ↔ ∃ y ∈ a, x = S.check y := by
  rw [← toOrdinary_mem_iff, toOrdinary_check, S.toForcingContext.mem_check_iff]
  constructor
  · rintro ⟨y, hy, he⟩
    exact ⟨y, hy, S.toOrdinary_injective he⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, rfl⟩

noncomputable def checkEmbedding (S : SymmetricContext V) : MembershipEndExtension V S.Model where
  toFun := S.check
  injective := fun _ _ h ↦ (S.check_eq_iff _ _).mp h
  mem_iff := S.check_mem_iff
  endExtension := fun x y h ↦ (S.mem_check_iff x y).mp h

end SymmetricContext
end ZFVP
