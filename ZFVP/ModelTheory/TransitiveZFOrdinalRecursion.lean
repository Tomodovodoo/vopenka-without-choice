import ZFVP.ModelTheory.TransitiveZFRankOperations
import ZFVP.ModelTheory.TransitiveZFBoundedQuantifiers
import ZFVP.SetTheory.UniformParameterizedRecursion

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
namespace TransitiveZF
variable (U : V) [IsTransitive U] [Nonempty (SetDomain U)] [(SetDomain U)↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem attempt_val (F : SetDomain U → SetDomain U) (G : V → V)
    (α f : SetDomain U) (hf : IsAttempt F α f)
    (hstep : ∀ g : SetDomain U, (F g).val = G g.val) : IsAttempt G α.val f.val := by
  refine ⟨(ordinal_iff U α).mp hf.1, (isFunction_iff U f).mp hf.2.1, ?_, ?_⟩
  · exact (domain_val U f).symm.trans (congrArg Subtype.val hf.2.2.1)
  · intro β hβ y
    let b : SetDomain U := ⟨β, (inferInstance : IsTransitive U).mem_trans hβ α.property⟩
    have hs : (F (f ↾ b)).val = G (f.val ↾ β) := by rw [hstep, restrict_val U]
    constructor
    · intro hy
      have hyU := (kpair_components_mem_transitive ((inferInstance : IsTransitive U).mem_trans hy f.property)).2
      let z : SetDomain U := ⟨y, hyU⟩
      have hz := (hf.2.2.2 b hβ z).mp ((kpair_mem_val_iff U b z f).mpr hy)
      exact (congrArg Subtype.val hz).trans hs
    · intro hy
      have hyU : y ∈ U := (hy.trans hs.symm) ▸ (F (f ↾ b)).property
      let z : SetDomain U := ⟨y, hyU⟩
      have hz : z = F (f ↾ b) := Subtype.ext (hy.trans hs.symm)
      exact (kpair_mem_val_iff U b z f).mp ((hf.2.2.2 b hβ z).mpr hz)

theorem transfiniteRec_val (F : SetDomain U → SetDomain U) (hF : ℒₛₑₜ-function₁ F)
    (G : V → V) (hG : ℒₛₑₜ-function₁ G) (α : SetDomain U) (hα : IsOrdinal α)
    (hstep : ∀ g : SetDomain U, (F g).val = G g.val) :
    (Replacement.transfiniteRec F hF α).val = Replacement.transfiniteRec G hG α.val := by
  let := hα
  obtain ⟨f, hf, he⟩ := (transfiniteRec_eq_iff F hF α (Replacement.transfiniteRec F hF α)).mp rfl |>.resolve_right
    (fun h ↦ h.1 hα)
  apply (transfiniteRec_eq_iff G hG α.val _).mpr
  exact Or.inl ⟨f.val, attempt_val U F G α f hf hstep,
    (congrArg Subtype.val he).trans (hstep f)⟩

theorem parameterRecursion_val (F : SetDomain U → SetDomain U → SetDomain U)
    (hF : ℒₛₑₜ-function₂ F) (G : V → V → V) (hG : ℒₛₑₜ-function₂ G)
    (a α : SetDomain U) (hα : IsOrdinal α)
    (hstep : ∀ g : SetDomain U, (F a g).val = G a.val g.val) :
    (parameterRecursion F hF a α).val = parameterRecursion G hG a.val α.val :=
  transfiniteRec_val U (F a) (by definability) (G a.val) (by definability) α hα hstep

end TransitiveZF
end ZFVP
