import ZFVP.ModelTheory.CohenModel
import ZFVP.ModelTheory.SymmetricModelGraph
import ZFVP.SetTheory.CohenFiniteAssignmentName

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace CohenModel

variable {G : Set V}
  (hG : IsExternalForcingGeneric (cohenConditions (ω : V)) (cohenOrder (ω : V)) G)

/-- The finite Cohen-real assignment after a ground permutation, evaluated in the symmetric model. -/
noncomputable def finiteAssignmentValue (E : V) (hEω : E ⊆ (ω : V))
    (hEf : IsInternallyFinite E) (b : V) (hb : IsInternalPermutation (ω : V) b) :
    (cohenContext (ω : V) G hG).Model :=
  (cohenContext (ω : V) G hG).ofName
    ⟨nameAction (cohenPermutation (ω : V) b) (cohenFiniteAssignmentName E),
      hereditarilySymmetric_nameAction (cohenGroup_group (ω : V)) (cohenFilter_normal (ω : V))
        ((mem_cohenGroup (ω : V) _).mpr ⟨b, hb, rfl⟩)
        (cohenFiniteAssignmentName_hereditarilySymmetric hEω hEf)⟩

theorem mem_finiteAssignmentValue_iff (E : V) (hEω : E ⊆ (ω : V))
    (hEf : IsInternallyFinite E) (b : V) (hb : IsInternalPermutation (ω : V) b)
    (z : (cohenContext (ω : V) G hG).Model) :
    z ∈ finiteAssignmentValue hG E hEω hEf b hb ↔ ∃ i : V, ∃ hi : i ∈ E,
      z = ⟨(cohenContext (ω : V) G hG).check i,
        real hG (b ‘ i) (function_value_mem hb.1 (hEω i hi))⟩ₖ := by
  let S := cohenContext (ω : V) G hG
  have hv (i : V) (hi : i ∈ E) :
      S.ofName ⟨orderedPairName ∅ (checkName ∅ i) (cohenRealName (ω : V) (b ‘ i)),
        hereditarilySymmetric_orderedPairName S.poset S.group S.normal S.top
          (hereditarilySymmetric_checkName S.poset S.group S.normal S.top i)
          (cohenRealName_hereditarilySymmetric (function_value_mem hb.1 (hEω i hi)))⟩ =
      ⟨S.check i, real hG (b ‘ i) (function_value_mem hb.1 (hEω i hi))⟩ₖ :=
    S.of_orderedPairName
      ⟨checkName ∅ i, hereditarilySymmetric_checkName S.poset S.group S.normal S.top i⟩
      ⟨cohenRealName (ω : V) (b ‘ i),
        cohenRealName_hereditarilySymmetric (function_value_mem hb.1 (hEω i hi))⟩
  rw [finiteAssignmentValue, S.mem_ofName_iff]
  constructor
  · rintro ⟨σ, p, _, hσp, hz⟩
    change ⟨σ.val, p⟩ₖ ∈ nameAction (cohenPermutation (ω : V) b) (cohenFiniteAssignmentName E) at hσp
    rw [nameAction_cohenFiniteAssignmentName hEω hb] at hσp
    obtain ⟨i, hi, he⟩ := (repl_spec _).mp hσp
    have he' : S.ofName σ = ⟨S.check i, real hG (b ‘ i) (function_value_mem hb.1 (hEω i hi))⟩ₖ := by
      rw [← hv i hi]
      exact congrArg S.ofName (Subtype.ext (kpair_iff.mp he).1)
    exact ⟨i, hi, hz.trans he'⟩
  · rintro ⟨i, hi, rfl⟩
    refine ⟨⟨orderedPairName ∅ (checkName ∅ i) (cohenRealName (ω : V) (b ‘ i)),
      hereditarilySymmetric_orderedPairName S.poset S.group S.normal S.top
        (hereditarilySymmetric_checkName S.poset S.group S.normal S.top i)
        (cohenRealName_hereditarilySymmetric (function_value_mem hb.1 (hEω i hi)))⟩,
      ∅, externalForcingFilter_top hG.1 (cohen_top (ω : V)), ?_, (hv i hi).symm⟩
    change ⟨orderedPairName ∅ (checkName ∅ i) (cohenRealName (ω : V) (b ‘ i)), (∅ : V)⟩ₖ ∈
      nameAction (cohenPermutation (ω : V) b) (cohenFiniteAssignmentName E)
    rw [nameAction_cohenFiniteAssignmentName hEω hb]
    exact (repl_spec _).mpr ⟨i, hi, rfl⟩

theorem finiteAssignmentValue_function (E : V) (hEω : E ⊆ (ω : V))
    (hEf : IsInternallyFinite E) (b : V) (hb : IsInternalPermutation (ω : V) b) :
    finiteAssignmentValue hG E hEω hEf b hb ∈
      reals hG ^ (cohenContext (ω : V) G hG).check E := by
  let S := cohenContext (ω : V) G hG
  apply mem_function.intro
  · intro z hz
    obtain ⟨i, hi, rfl⟩ := (mem_finiteAssignmentValue_iff hG E hEω hEf b hb z).mp hz
    exact kpair_mem_iff.mpr ⟨(S.check_mem_iff i E).mpr hi,
      (mem_reals_iff hG _).mpr ⟨b ‘ i, function_value_mem hb.1 (hEω i hi), rfl⟩⟩
  · intro x hx
    obtain ⟨i, hi, rfl⟩ := (S.mem_check_iff E x).mp hx
    refine ⟨real hG (b ‘ i) (function_value_mem hb.1 (hEω i hi)),
      (mem_finiteAssignmentValue_iff hG E hEω hEf b hb _).mpr ⟨i, hi, rfl⟩, ?_⟩
    intro y hy
    obtain ⟨j, hj, he⟩ := (mem_finiteAssignmentValue_iff hG E hEω hEf b hb _).mp hy
    obtain ⟨hij, hyj⟩ := kpair_iff.mp he
    obtain rfl := (S.check_eq_iff i j).mp hij
    exact hyj

theorem finiteAssignmentValue_value (E : V) (hEω : E ⊆ (ω : V))
    (hEf : IsInternallyFinite E) (b : V) (hb : IsInternalPermutation (ω : V) b)
    {i : V} (hi : i ∈ E) :
    (finiteAssignmentValue hG E hEω hEf b hb) ‘ ((cohenContext (ω : V) G hG).check i) =
      real hG (b ‘ i) (function_value_mem hb.1 (hEω i hi)) := by
  have : IsFunction (finiteAssignmentValue hG E hEω hEf b hb) :=
    IsFunction.of_mem (finiteAssignmentValue_function hG E hEω hEf b hb)
  exact value_eq_of_kpair_mem
    ((mem_finiteAssignmentValue_iff hG E hEω hEf b hb _).mpr ⟨i, hi, rfl⟩)

theorem finiteAssignmentValue_injective (E : V) (hEω : E ⊆ (ω : V))
    (hEf : IsInternallyFinite E) (b : V) (hb : IsInternalPermutation (ω : V) b) :
    Injective (finiteAssignmentValue hG E hEω hEf b hb) := by
  let S := cohenContext (ω : V) G hG
  intro x y z hx hy
  obtain ⟨i, hi, hxi⟩ := (mem_finiteAssignmentValue_iff hG E hEω hEf b hb _).mp hx
  obtain ⟨j, hj, hyj⟩ := (mem_finiteAssignmentValue_iff hG E hEω hEf b hb _).mp hy
  obtain ⟨hxi, hzi⟩ := kpair_iff.mp hxi
  obtain ⟨hyj, hzj⟩ := kpair_iff.mp hyj
  have hbij := (real_eq_iff hG (function_value_mem hb.1 (hEω i hi))
    (function_value_mem hb.1 (hEω j hj))).mp (hzi.symm.trans hzj)
  have hij := injective_value_eq hb.1 hb.2.1 (hEω i hi) (hEω j hj) hbij
  exact hxi.trans ((congrArg S.check hij).trans hyj.symm)

/-- Equal evaluated assignments identify the original coordinate permutations on their domain. -/
theorem finiteAssignmentValue_eq_implies_agree (E : V) (hEω : E ⊆ (ω : V))
    (hEf : IsInternallyFinite E) (b : V) (hb : IsInternalPermutation (ω : V) b)
    (c : V) (hc : IsInternalPermutation (ω : V) c)
    (he : finiteAssignmentValue hG E hEω hEf b hb = finiteAssignmentValue hG E hEω hEf c hc) :
    ∀ i ∈ E, b ‘ i = c ‘ i := by
  intro i hi
  have hv := congrArg (fun f : (cohenContext (ω : V) G hG).Model ↦
    f ‘ ((cohenContext (ω : V) G hG).check i)) he
  rw [finiteAssignmentValue_value hG E hEω hEf b hb hi,
    finiteAssignmentValue_value hG E hEω hEf c hc hi] at hv
  exact (real_eq_iff hG (function_value_mem hb.1 (hEω i hi))
    (function_value_mem hc.1 (hEω i hi))).mp hv

theorem finiteAssignmentValue_eq_of_agree (E : V) (hEω : E ⊆ (ω : V))
    (hEf : IsInternallyFinite E) (b : V) (hb : IsInternalPermutation (ω : V) b)
    (c : V) (hc : IsInternalPermutation (ω : V) c)
    (hagree : ∀ i ∈ E, b ‘ i = c ‘ i) :
    finiteAssignmentValue hG E hEω hEf b hb = finiteAssignmentValue hG E hEω hEf c hc := by
  apply congrArg (cohenContext (ω : V) G hG).ofName
  exact Subtype.ext (nameAction_cohenFiniteAssignmentName_eq_of_agree hEω hb hc hagree)

end CohenModel
end ZFVP

