import ZFVP.SetTheory.HODModelsZF
import ZFVP.SetTheory.EndExtensionCoding

/-! Dependent choice in the hereditarily ordinal definable sets: the inclusion of a transitive class
is a membership end extension, so the bounded vocabulary (pairs, `ω`, function spaces, values) is
absolute; dependent choice in `V` then transfers to HOD as soon as HOD is closed under
`ω`-sequences of its elements. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- The inclusion of a transitive class is a membership end extension. -/
def classDomain_endExtension (H : SetTheorySemisentence 2) (a : V)
    (htrans : ∀ x, classOf H a x → ∀ y ∈ x, classOf H a y) :
    MembershipEndExtension (ClassDomain (classOf H a)) V where
  toFun := Subtype.val
  injective := Subtype.val_injective
  mem_iff := fun _ _ ↦ Iff.rfl
  endExtension := fun x y hy ↦ ⟨⟨y, htrans _ x.property y hy⟩, hy, rfl⟩

section

variable (Pf : SetTheorySemisentence 2) (p : V)

theorem hod_transitive : ∀ x, classOf (hodFormula Pf) p x → ∀ y ∈ x, classOf (hodFormula Pf) p y :=
  fun x hx y hy ↦ (hodClass_iff Pf p y).mpr (((hodClass_iff Pf p x).mp hx).mem Pf hy)

local notation "HODDomain" => ClassDomain (classOf (hodFormula Pf) p)

/-- Dependent choice holds in HOD when it holds in `V` and HOD is closed under `ω`-sequences of
its elements. -/
theorem hod_dependentChoice [Nonempty HODDomain] [HODDomain↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
    (hDC : InternalDependentChoice V)
    (hseq : ∀ f A : V, f ∈ A ^ (ω : V) → (∀ n ∈ (ω : V), IsHOD Pf (f ‘ n) p) → IsHOD Pf f p) :
    InternalDependentChoice HODDomain := by
  let j := classDomain_endExtension (hodFormula Pf) p (hod_transitive Pf p)
  intro A R hA hR
  have hA' : IsNonempty A.val := ⟨by obtain ⟨x, hx⟩ := hA.nonempty; exact ⟨x.val, hx⟩⟩
  have hR' : ∀ x ∈ A.val, ∃ y ∈ A.val, ⟨x, y⟩ₖ ∈ R.val := by
    intro x hx
    let x' : HODDomain := ⟨x, hod_transitive Pf p _ A.property x hx⟩
    obtain ⟨y, hy, hxy⟩ := hR x' hx
    refine ⟨y.val, hy, ?_⟩
    have hk : (⟨x', y⟩ₖ : HODDomain).val = ⟨x, y.val⟩ₖ := j.map_kpair x' y
    have h : (⟨x', y⟩ₖ : HODDomain).val ∈ R.val := hxy
    rw [hk] at h
    exact h
  obtain ⟨f, hf, hchain⟩ := hDC A.val R.val hA' hR'
  have hfun : IsFunction f := IsFunction.of_mem hf
  have hdom : domain f = (ω : V) := domain_eq_of_mem_function hf
  have hvals : ∀ n ∈ (ω : V), IsHOD Pf (f ‘ n) p := fun n hn ↦
    (hodClass_iff Pf p _).mp (hod_transitive Pf p _ A.property _ (function_value_mem hf hn))
  have hfH : classOf (hodFormula Pf) p f := (hodClass_iff Pf p f).mpr (hseq f A.val hf hvals)
  let F : HODDomain := ⟨f, hfH⟩
  have hjω : (ω : HODDomain).val = (ω : V) := j.map_omega
  have hF : F ∈ A ^ (ω : HODDomain) := by
    apply (j.function_iff F (ω : HODDomain) A).mp
    show f ∈ A.val ^ (ω : HODDomain).val
    rw [hjω]
    exact hf
  obtain ⟨hFfun, hFdom⟩ := (j.function_on_iff F (ω : HODDomain)).mp
    ⟨hfun, by show domain f = (ω : HODDomain).val; rw [hjω]; exact hdom⟩
  refine ⟨F, hF, fun n hn ↦ ?_⟩
  have hn' : n.val ∈ (ω : V) := (j.natural_iff n).mpr hn
  have hsn : succ n ∈ (ω : HODDomain) := ω_succ_closed hn
  have hs : (succ n : HODDomain).val = succ n.val := j.map_succ n
  have h1 : (F ‘ n).val = f ‘ n.val := j.map_value F n (by rw [hFdom]; exact hn)
  have h2 : (F ‘ (succ n)).val = f ‘ (succ n.val) := by
    have h := j.map_value F (succ n) (by rw [hFdom]; exact hsn)
    calc (F ‘ (succ n)).val = f ‘ ((succ n : HODDomain).val) := h
      _ = f ‘ (succ n.val) := by rw [hs]
  have hk : (⟨F ‘ n, F ‘ (succ n)⟩ₖ : HODDomain).val = ⟨(F ‘ n).val, (F ‘ (succ n)).val⟩ₖ :=
    j.map_kpair _ _
  show (⟨F ‘ n, F ‘ (succ n)⟩ₖ : HODDomain).val ∈ R.val
  rw [hk, h1, h2]
  exact hchain n.val hn'

end

end ZFVP
