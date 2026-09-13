import ZFVP.ModelTheory.SymmetricLiftDomainClosure
import ZFVP.SetTheory.BoundedFunctionDomain

/-! Bounded elementarity of the internal symmetric graph, derived from the ordinary lift. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace SymmetricLiftData

variable {S : SymmetricContext V} {U W f : V}
variable [IsTransitive U] [IsTransitive W]
variable [Nonempty (SetDomain U)] [Nonempty (SetDomain W)]
variable [(SetDomain U)↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [(SetDomain W)↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable (L : SymmetricLiftData S U W f)

theorem graph_bounded_elementary {n : ℕ} {φ : SetTheorySemisentence n}
    (hφ : IsBoundedSetFormula φ) (v : Fin n → S.Model) (hv : ∀ i, v i ∈ domain L.graph) :
    φ.Evalb v ↔ φ.Evalb (fun i ↦ L.graph ‘ (v i)) := by
  choose b hb using fun i ↦ L.graph_domain_source (v i) (hv i)
  have hs : (fun i ↦ L.sourceInclusion (b i)) = (fun i ↦ S.inclusion (v i)) := funext hb
  have ht : (fun i ↦ L.targetInclusion (L.ordinaryLift (b i))) =
      (fun i ↦ S.inclusion (L.graph ‘ (v i))) := by
    funext i
    exact (L.graph_agrees_ordinaryLift (v i) (hv i) (b i) (hb i)).symm
  have hj : φ.Evalb b ↔ φ.Evalb (fun i ↦ L.ordinaryLift (b i)) := by
    have he := L.ordinaryLift.elementary φ b (Empty.elim : Empty → L.sourceContext.Model)
    have hf : L.ordinaryLift ∘ (Empty.elim : Empty → L.sourceContext.Model) =
        (Empty.elim : Empty → L.targetContext.Model) := funext (fun e ↦ Empty.elim e)
    rw [hf] at he
    exact he
  exact (S.inclusion.bounded_elementary hφ v).trans
    ((hs ▸ L.sourceInclusion.bounded_elementary hφ b).symm.trans
      (hj.trans ((ht ▸ L.targetInclusion.bounded_elementary hφ (fun i ↦ L.ordinaryLift (b i))).trans
        (S.inclusion.bounded_elementary hφ _).symm)))

theorem graph_bounded_defined_iff {n : ℕ} {φ : SetTheorySemisentence n}
    (hφ : IsBoundedSetFormula φ) (R : (Fin n → S.Model) → Prop) [Defined R φ]
    (v : Fin n → S.Model) (hv : ∀ i, v i ∈ domain L.graph) :
    R v ↔ R (fun i ↦ L.graph ‘ (v i)) :=
  (Defined.eval_iff v).symm.trans ((L.graph_bounded_elementary hφ v hv).trans (Defined.eval_iff _))

theorem graph_value_empty : L.graph ‘ (∅ : S.Model) = ∅ :=
  (L.graph_bounded_defined_iff boundedEmptyFormula_bounded (fun v ↦ v 0 = ∅)
    ![∅] (by simp [IsCodingSupport.empty_mem])).mp rfl

theorem graph_value_mem_iff {x y : S.Model} (hx : x ∈ domain L.graph) (hy : y ∈ domain L.graph) :
    L.graph ‘ x ∈ L.graph ‘ y ↔ x ∈ y := by
  have h := L.graph_bounded_elementary
    (IsBoundedSetFormula.rel Language.Set.Rel.mem ![.bvar 0, .bvar 1]) ![x, y] (by simp [hx, hy])
  exact h.symm

theorem graph_value_eq_iff {x y : S.Model} (hx : x ∈ domain L.graph) (hy : y ∈ domain L.graph) :
    L.graph ‘ x = L.graph ‘ y ↔ x = y := by
  have h := L.graph_bounded_elementary
    (IsBoundedSetFormula.rel Language.Set.Rel.eq ![.bvar 0, .bvar 1]) ![x, y] (by simp [hx, hy])
  exact h.symm

theorem graph_value_pair {x y : S.Model} (hx : x ∈ domain L.graph) (hy : y ∈ domain L.graph) :
    L.graph ‘ ⟨x, y⟩ₖ = ⟨L.graph ‘ x, L.graph ‘ y⟩ₖ :=
  (L.graph_bounded_defined_iff boundedKpairFormula_bounded
    (fun v ↦ v 0 = ⟨v 1, v 2⟩ₖ) ![⟨x, y⟩ₖ, x, y]
      (by simp [Fin.forall_fin_iff_zero_and_forall_succ, hx, hy,
        IsCodingSupport.kpair_closed _ hx _ hy])).mp rfl

theorem graph_value_doubleton {x y : S.Model} (hx : x ∈ domain L.graph) (hy : y ∈ domain L.graph) :
    L.graph ‘ (doubleton x y) = doubleton (L.graph ‘ x) (L.graph ‘ y) :=
  (L.graph_bounded_defined_iff boundedDoubletonFormula_bounded
    (fun v ↦ v 0 = doubleton (v 1) (v 2)) ![doubleton x y, x, y]
      (by simp [Fin.forall_fin_iff_zero_and_forall_succ, hx, hy,
        IsCodingSupport.doubleton_closed _ hx _ hy])).mp rfl

theorem graph_value_succ {x : S.Model} (hx : x ∈ domain L.graph) :
    L.graph ‘ (succ x) = succ (L.graph ‘ x) :=
  (L.graph_bounded_defined_iff boundedSuccFormula_bounded
    (fun v ↦ v 0 = succ (v 1)) ![succ x, x]
      (by simp [hx, IsCodingSupport.succ_closed _ hx])).mp rfl

theorem graph_value_omega : L.graph ‘ (ω : S.Model) = ω :=
  (L.graph_bounded_defined_iff boundedOmegaFormula_bounded (fun v ↦ v 0 = ω)
    ![ω] (by simp [L.graph_domain_omega])).mp rfl

theorem graph_value_natural {n : S.Model} (hn : n ∈ (ω : S.Model)) : L.graph ‘ n = n := by
  apply naturalNumber_induction (fun n ↦ L.graph ‘ n = n) (by definability) L.graph_value_empty ?_ n hn
  intro i hi ih
  rw [L.graph_value_succ (IsCodingSupport.natural_mem hi), ih]

theorem graph_value_numeral (n : ℕ) : L.graph ‘ (n : S.Model) = (n : S.Model) :=
  L.graph_value_natural (by simp)

theorem graph_value_function_domain {g A : S.Model} (hg : g ∈ domain L.graph)
    (hA : A ∈ domain L.graph) (hfunc : IsFunction g) (hdom : domain g = A) :
    IsFunction (L.graph ‘ g) ∧ domain (L.graph ‘ g) = L.graph ‘ A :=
  (L.graph_bounded_defined_iff boundedFunctionDomainFormula_bounded
    (fun v ↦ IsFunction (v 0) ∧ domain (v 0) = v 1) ![g, A] (by simp [hg, hA])).mp ⟨hfunc, hdom⟩

end SymmetricLiftData
end ZFVP
