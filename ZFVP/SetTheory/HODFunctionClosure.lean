import ZFVP.SetTheory.HODReals

/-! Hereditary ordinal definability of functions. An ordinal definable function whose domain and
values are hereditarily ordinal definable is itself hereditarily ordinal definable, and a function
`f : ω → A` is ordinal definable as soon as `A`, an injection `e` defined on `A` and the composite
`e ∘ f` are, because `f` can then be read off from the composite. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- The graph of `f : ω → A` recovered from an injection `e` on `A` and the composite `g = e ∘ f`,
as a formula in the parameters `A`, `e`, `g`. -/
def compCodeFormula : SetTheorySemisentence 4 :=
  f“z A e g. ∃ n ∈ !isω, ∃ x ∈ A, z = !kpair.dfn n x ∧ !value.dfn e x = !value.dfn g n”

theorem eval_compCodeFormula (z A e g : V) :
    compCodeFormula.Evalb ![z, A, e, g] ↔
      ∃ n ∈ (ω : V), ∃ x ∈ A, z = ⟨n, x⟩ₖ ∧ e ‘ x = g ‘ n := by
  simp [compCodeFormula]

section

variable (Pf : SetTheorySemisentence 2) (p : V)

/-- An ordinal definable function with hereditarily ordinal definable domain and values is
hereditarily ordinal definable. -/
theorem isHOD_of_function {f : V} [IsFunction f] (hf : IsOD Pf f p)
    (hdom : IsHOD Pf (domain f) p) (hval : ∀ n ∈ domain f, IsHOD Pf (f ‘ n) p) :
    IsHOD Pf f p := by
  refine isHOD_of_od Pf hf (fun q hq ↦ ?_)
  obtain ⟨n, hn, i, -, rfl⟩ :=
    mem_prod_iff.mp ((mem_function_iff.mp (isFunction_iff.mp ‹IsFunction f›)).1 q hq)
  have hi : i = f ‘ n := (value_eq_of_kpair_mem hq).symm
  rw [hi]
  exact isHOD_kpair Pf p (hdom.mem Pf hn) (hval n hn)

/-- A function `f : ω → A` is ordinal definable when `A`, an injection `e` on `A` and the
composite `g = e ∘ f` are. -/
theorem isOD_of_injective_comp {A B e f g : V} (hA : IsOD Pf A p) (he : IsOD Pf e p)
    (hg : IsOD Pf g p) (hf : f ∈ A ^ (ω : V)) (he' : e ∈ B ^ A) (heinj : Injective e)
    (hcomp : ∀ n ∈ (ω : V), g ‘ n = e ‘ (f ‘ n)) [IsFunction g] : IsOD Pf f p := by
  have hff : IsFunction f := IsFunction.of_mem hf
  have hfd : domain f = (ω : V) := domain_eq_of_mem_function hf
  refine isOD_of_definable_cons Pf compCodeFormula (q := ![A, e, g]) ?_ ?_
  · intro i
    refine Fin.cases hA (fun j ↦ ?_) i
    refine Fin.cases he (fun k ↦ ?_) j
    exact Fin.cases hg (fun t ↦ t.elim0) k
  · intro y
    show y ∈ f ↔ compCodeFormula.Evalb ![y, A, e, g]
    rw [eval_compCodeFormula]
    constructor
    · intro hy
      obtain ⟨n, hn, x, hx, rfl⟩ := mem_prod_iff.mp ((mem_function_iff.mp hf).1 y hy)
      have hxv : x = f ‘ n := (value_eq_of_kpair_mem hy).symm
      exact ⟨n, hn, x, hx, rfl, by rw [hxv, hcomp n hn]⟩
    · rintro ⟨n, hn, x, hx, rfl, hval⟩
      have hxn : x = f ‘ n :=
        injective_value_eq he' heinj hx (function_value_mem hf hn) (hval.trans (hcomp n hn))
      rw [hxn]
      exact kpair_value_mem (by rw [hfd]; exact hn)

/-- The hereditary version: if in addition `A` is hereditarily ordinal definable, so is `f`. -/
theorem isHOD_of_injective_comp {A B e f g : V} (hA : IsHOD Pf A p) (he : IsOD Pf e p)
    (hg : IsOD Pf g p) (hf : f ∈ A ^ (ω : V)) (he' : e ∈ B ^ A) (heinj : Injective e)
    (hcomp : ∀ n ∈ (ω : V), g ‘ n = e ‘ (f ‘ n)) [IsFunction g] : IsHOD Pf f p := by
  have hff : IsFunction f := IsFunction.of_mem hf
  have hfd : domain f = (ω : V) := domain_eq_of_mem_function hf
  refine isHOD_of_function Pf p
    (isOD_of_injective_comp Pf p (IsHOD.od Pf hA) he hg hf he' heinj hcomp) ?_ ?_
  · rw [hfd]
    exact isHOD_of_ordinal Pf ω p
  · intro n hn
    rw [hfd] at hn
    exact hA.mem Pf (function_value_mem hf hn)

end

end ZFVP
