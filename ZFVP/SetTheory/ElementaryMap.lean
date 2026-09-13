import ZFVP.SetTheory.Relativization

/-! Elementary maps for the membership language used by Foundation. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

/-- A map preserving and reflecting satisfaction of every first-order formula.
This is the definition of elementarity; no existence of such a map is asserted. -/
structure ElementaryMap (V W : Type*) [SetStructure V] [SetStructure W] where
  toFun : V → W
  elementary : ∀ {ξ : Type} {n : ℕ} (φ : SetTheorySemiformula ξ n)
    (b : Fin n → V) (f : ξ → V),
    φ.Eval b f ↔ φ.Eval (toFun ∘ b) (toFun ∘ f)

instance {V W : Type*} [SetStructure V] [SetStructure W] :
    CoeFun (ElementaryMap V W) (fun _ ↦ V → W) := ⟨ElementaryMap.toFun⟩

namespace ElementaryMap

variable {V W U : Type*} [SetStructure V] [SetStructure W] [SetStructure U]

theorem map_eq_iff (j : ElementaryMap V W) (x y : V) : j x = j y ↔ x = y := by
  have h := j.elementary (.rel Language.Set.Rel.eq ![.bvar 0, .bvar 1])
    ![x, y] (Empty.elim : Empty → V)
  exact h.symm

theorem injective (j : ElementaryMap V W) : Function.Injective j :=
  fun _ _ h ↦ (j.map_eq_iff _ _).mp h

theorem map_mem_iff (j : ElementaryMap V W) (x y : V) : j x ∈ j y ↔ x ∈ y := by
  have h := j.elementary (.rel Language.Set.Rel.mem ![.bvar 0, .bvar 1])
    ![x, y] (Empty.elim : Empty → V)
  exact h.symm

def identity (V : Type*) [SetStructure V] : ElementaryMap V V where
  toFun := id
  elementary _ _ _ := Iff.rfl

def comp (k : ElementaryMap W U) (j : ElementaryMap V W) : ElementaryMap V U where
  toFun := k ∘ j
  elementary φ b f := (j.elementary φ b f).trans (k.elementary φ (j ∘ b) (j ∘ f))

/-- The underlying restricted function lands in the image set by atomic elementarity. -/
def restrictFun (j : ElementaryMap V W) (a : V) : SetDomain a → SetDomain (j a) :=
  fun x ↦ ⟨j x.val, (j.map_mem_iff x.val a).mpr x.property⟩

/-- Restricting an elementary map to a set is elementary into the image set.
The target is all elements of `j a`, which need not equal the pointwise image of `a`. -/
def restrict (j : ElementaryMap V W) (a : V) :
    ElementaryMap (SetDomain a) (SetDomain (j a)) where
  toFun := j.restrictFun a
  elementary φ b f := by
    rw [← eval_relativize a φ b f,
      ← eval_relativize (j a) φ (j.restrictFun a ∘ b) (j.restrictFun a ∘ f)]
    have h := j.elementary (relativize φ) (fun i ↦ (b i).val)
      (fun x ↦ x.elim a (fun i ↦ (f i).val))
    have hf : (fun x : Option _ ↦ x.elim (j a) (fun i ↦ j (f i).val)) =
        (j ∘ fun x ↦ x.elim a (fun i ↦ (f i).val)) := by
      funext x
      cases x <;> rfl
    change _ ↔ (relativize φ).Eval (j ∘ fun i ↦ (b i).val) (fun x ↦ x.elim (j a) (fun i ↦ j (f i).val))
    rw [hf]
    exact h

end ElementaryMap
end ZFVP


