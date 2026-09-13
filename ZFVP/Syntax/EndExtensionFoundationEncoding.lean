import ZFVP.Syntax.EndExtensionAssignments
import ZFVP.Syntax.EndExtensionFormulas
import ZFVP.Syntax.FoundationEncoding

/-! Standard finite syntax commutes with every membership end extension. -/

namespace ZFVP.MembershipEndExtension
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V W : Type*} [SetStructure V] [SetStructure W]
  [Nonempty V] [Nonempty W] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {Λ : Language} {ξ : Type*}

theorem map_encodeSemiterm (j : MembershipEndExtension V W)
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

theorem map_encodeSemiformula (j : MembershipEndExtension V W)
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

end ZFVP.MembershipEndExtension
