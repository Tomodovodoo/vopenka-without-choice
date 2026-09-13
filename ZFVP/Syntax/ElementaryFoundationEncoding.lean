import ZFVP.Syntax.UniformSyntaxTransport
import ZFVP.SetTheory.ElementaryDefined
import ZFVP.Syntax.FoundationEncoding

/-! Elementary maps preserve the constructors of standard finite syntax. -/
namespace ZFVP.ElementaryMap
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V W : Type*} [SetStructure V] [SetStructure W]
  [Nonempty V] [Nonempty W] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem map_kpair (j : ElementaryMap V W) (x y : V) : j ⟨x, y⟩ₖ = ⟨j x, j y⟩ₖ :=
  j.map_definedFunction kpair.dfn (fun v ↦ ⟨v 0, v 1⟩ₖ) (fun v ↦ ⟨v 0, v 1⟩ₖ) ![x, y]

theorem map_first (j : ElementaryMap V W) (p : V) : j (kpair.π₁ p) = kpair.π₁ (j p) :=
  j.map_definedFunction₁ kpair.π₁.dfn kpair.π₁ kpair.π₁ p

theorem map_second (j : ElementaryMap V W) (p : V) : j (kpair.π₂ p) = kpair.π₂ (j p) :=
  j.map_definedFunction₁ kpair.π₂.dfn kpair.π₂ kpair.π₂ p

theorem map_omega (j : ElementaryMap V W) : j (ω : V) = (ω : W) :=
  (j.map_defined isω (fun v ↦ v 0 = (ω : V)) (fun v ↦ v 0 = (ω : W)) ![ω]).mp rfl

theorem function_iff (j : ElementaryMap V W) (f : V) : IsFunction (j f) ↔ IsFunction f :=
  (j.map_defined IsFunction.dfn (fun v ↦ IsFunction (v 0)) (fun v ↦ IsFunction (v 0)) ![f]).symm

theorem map_domain (j : ElementaryMap V W) (f : V) : j (domain f) = domain (j f) :=
  j.map_definedFunction₁ domain.dfn domain domain f

theorem map_value (j : ElementaryMap V W) (f x : V) : j (f ‘ x) = (j f) ‘ (j x) :=
  j.map_definedFunction value.dfn (fun v ↦ (v 0) ‘ (v 1)) (fun v ↦ (v 0) ‘ (v 1)) ![f, x]

theorem map_boundVarCode (j : ElementaryMap V W) (i : V) : j (boundVarCode i) = boundVarCode (j i) :=
  j.map_definedFunction₁ boundVarCodeFormula boundVarCode boundVarCode i

theorem map_freeVarCode (j : ElementaryMap V W) (i : V) : j (freeVarCode i) = freeVarCode (j i) :=
  j.map_definedFunction₁ freeVarCodeFormula freeVarCode freeVarCode i

theorem map_functionTermCode (j : ElementaryMap V W) (f args : V) :
    j (functionTermCode f args) = functionTermCode (j f) (j args) :=
  j.map_definedFunction functionTermCodeFormula (fun v ↦ functionTermCode (v 0) (v 1))
    (fun v ↦ functionTermCode (v 0) (v 1)) ![f, args]

theorem map_relationToken (j : ElementaryMap V W) (r : V) : j (relationToken r) = relationToken (j r) :=
  j.map_definedFunction₁ relationTokenFormula relationToken relationToken r

theorem map_truthCode (j : ElementaryMap V W) : j (truthCode : V) = (truthCode : W) :=
  (j.map_defined truthCodeFormula (fun v ↦ v 0 = (truthCode : V))
    (fun v ↦ v 0 = (truthCode : W)) ![truthCode]).mp rfl

theorem map_falsityCode (j : ElementaryMap V W) : j (falsityCode : V) = (falsityCode : W) :=
  (j.map_defined falsityCodeFormula (fun v ↦ v 0 = (falsityCode : V))
    (fun v ↦ v 0 = (falsityCode : W)) ![falsityCode]).mp rfl

theorem map_atomCode (j : ElementaryMap V W) (r args : V) : j (atomCode r args) = atomCode (j r) (j args) :=
  j.map_definedFunction atomCodeFormula (fun v ↦ atomCode (v 0) (v 1))
    (fun v ↦ atomCode (v 0) (v 1)) ![r, args]

theorem map_negAtomCode (j : ElementaryMap V W) (r args : V) : j (negAtomCode r args) = negAtomCode (j r) (j args) :=
  j.map_definedFunction negAtomCodeFormula (fun v ↦ negAtomCode (v 0) (v 1))
    (fun v ↦ negAtomCode (v 0) (v 1)) ![r, args]

theorem map_andCode (j : ElementaryMap V W) (φ ψ : V) : j (andCode φ ψ) = andCode (j φ) (j ψ) :=
  j.map_definedFunction andCodeFormula (fun v ↦ andCode (v 0) (v 1))
    (fun v ↦ andCode (v 0) (v 1)) ![φ, ψ]

theorem map_orCode (j : ElementaryMap V W) (φ ψ : V) : j (orCode φ ψ) = orCode (j φ) (j ψ) :=
  j.map_definedFunction orCodeFormula (fun v ↦ orCode (v 0) (v 1))
    (fun v ↦ orCode (v 0) (v 1)) ![φ, ψ]

theorem map_allCode (j : ElementaryMap V W) (φ : V) : j (allCode φ) = allCode (j φ) :=
  j.map_definedFunction₁ allCodeFormula allCode allCode φ

theorem map_existsCode (j : ElementaryMap V W) (φ : V) : j (existsCode φ) = existsCode (j φ) :=
  j.map_definedFunction₁ existsCodeFormula existsCode existsCode φ

variable {Λ : Language} {ξ : Type*}
theorem map_encodeSemiterm (j : ElementaryMap V W)
    (F : ∀ {k}, Λ.Func k → V) (e : ξ → V) {n} (t : Semiterm Λ ξ n) :
    j (encodeSemiterm F e t) = encodeSemiterm (fun f ↦ j (F f)) (j ∘ e) t := by
  induction t with
  | bvar i => simp only [encodeSemiterm, j.map_boundVarCode, j.map_numeral]
  | fvar x => exact j.map_freeVarCode (e x)
  | func f ts ih =>
    simp only [encodeSemiterm, j.map_functionTermCode, j.map_standardTuple]
    congr 1
    congr 1
    funext i
    exact ih i

theorem map_encodeSemiformula (j : ElementaryMap V W)
    (F : ∀ {k}, Λ.Func k → V) (R : ∀ {k}, Λ.Rel k → V) (e : ξ → V)
    {n} (φ : Semiformula Λ ξ n) :
    j (encodeSemiformula F R e φ) =
      encodeSemiformula (fun f ↦ j (F f)) (fun r ↦ j (R r)) (j ∘ e) φ := by
  induction φ with
  | verum => exact j.map_truthCode
  | falsum => exact j.map_falsityCode
  | rel r ts =>
    simp only [encodeSemiformula, j.map_atomCode, j.map_relationToken, j.map_standardTuple]
    congr 1
    congr 1
    funext i
    exact j.map_encodeSemiterm F e (ts i)
  | nrel r ts =>
    simp only [encodeSemiformula, j.map_negAtomCode, j.map_relationToken, j.map_standardTuple]
    congr 1
    congr 1
    funext i
    exact j.map_encodeSemiterm F e (ts i)
  | and φ ψ ihφ ihψ => simp only [encodeSemiformula, j.map_andCode, ihφ, ihψ]
  | or φ ψ ihφ ihψ => simp only [encodeSemiformula, j.map_orCode, ihφ, ihψ]
  | all φ ih => simp only [encodeSemiformula, j.map_allCode, ih]
  | exs φ ih => simp only [encodeSemiformula, j.map_existsCode, ih]


end ZFVP.ElementaryMap


