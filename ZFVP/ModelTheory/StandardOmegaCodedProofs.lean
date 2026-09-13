import ZFVP.ModelTheory.EqualityCodedSequentProofs
import ZFVP.ModelTheory.StandardCodedRules
import ZFVP.ModelTheory.SchmerlStandardOmega

/-! In an omega-standard ambient model, every internal finite proof is an
external finite list of its actual internal lines. Its formulas remain raw codes. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem standardList_prefix_values_append {p y : V} [IsFunction p] {k : ℕ}
    (hd : domain p = ((k + 1 : ℕ) : V)) (hy : p ‘ (k : V) = y) :
    standardList ((List.ofFn (fun i : Fin k ↦ p ‘ (i.val : V))) ++ [y]) = p := by
  apply functions_eq_of_domain_values (by simp [hd])
  intro i hi
  rw [domain_standardList] at hi
  have hi' : i ∈ ((k + 1 : ℕ) : V) := by simpa using hi
  obtain ⟨j, rfl⟩ := (mem_natCast_iff i (k + 1)).mp hi'
  have hj : j.val < (List.ofFn (fun i : Fin k ↦ p ‘ (i.val : V)) ++ [y]).length := by
    simpa using j.isLt
  rw [value_standardList _ ⟨j.val, hj⟩]
  by_cases h : j.val < k
  · have hlen : j.val < (List.ofFn (fun i : Fin k ↦ p ‘ (i.val : V))).length := by simpa using h
    simp only [List.get_eq_getElem, List.getElem_append_left hlen, List.getElem_ofFn]
  · have he : j.val = k := by omega
    simpa [List.get_eq_getElem, he] using hy.symm

theorem IsOpenCodedSequentProof.to_standard {T p n Γ : V}
    (hp : IsOpenCodedSequentProof T p n Γ) (hω : Schmerl.HasStandardOmega V) :
    StandardCodedProvable T n Γ := by
  obtain ⟨hf, l, hl, hd, he, hs⟩ := hp
  let := hf
  obtain ⟨k, rfl⟩ := hω l hl
  let xs := List.ofFn (fun i : Fin k ↦ p ‘ (i.val : V))
  have hlist : standardList (xs ++ [⟨n, Γ⟩ₖ]) = p :=
    standardList_prefix_values_append (by simpa only [num_succ_def] using hd) he
  refine ⟨xs, fun i ↦ ?_⟩
  have hi : (i.val : V) ∈ domain p := by
    rw [← hlist, domain_standardList]
    exact natCast_mem_of_lt i.isLt
  obtain ⟨m, Δ, hv, hc, hr⟩ := hs (i.val : V) hi
  refine ⟨m, Δ, ?_, hc, ?_⟩
  · rw [← hlist, value_standardList] at hv
    exact hv
  · rw [← hlist, range_restrict_standardList] at hr
    exact hr

theorem standardCodedProvable_iff_internal (hω : Schmerl.HasStandardOmega V) (T n Γ : V) :
    StandardCodedProvable T n Γ ↔ ∃ p, IsOpenCodedSequentProof T p n Γ :=
  ⟨StandardCodedProvable.to_internal, fun ⟨_, hp⟩ ↦ hp.to_standard hω⟩

theorem openCodedSequentConsistent_iff_no_standard_refutation
    (hω : Schmerl.HasStandardOmega V) (T : V) :
    OpenCodedSequentConsistent T ↔ ¬StandardCodedProvable T 0 ∅ :=
  not_congr (standardCodedProvable_iff_internal hω T 0 ∅).symm

theorem IsEqualityCodedSequentProof.to_standard {T p n Γ : V}
    (hp : IsEqualityCodedSequentProof T p n Γ) (hω : Schmerl.HasStandardOmega V) :
    StandardCodedProvable (T ∪ canonicalEqualityOpenCodes) n Γ :=
  IsOpenCodedSequentProof.to_standard hp hω

theorem equalityCodedSequentConsistent_iff_no_standard_refutation
    (hω : Schmerl.HasStandardOmega V) (T : V) :
    EqualityCodedSequentConsistent T ↔ ¬StandardCodedProvable (T ∪ canonicalEqualityOpenCodes) 0 ∅ :=
  openCodedSequentConsistent_iff_no_standard_refutation hω _

end ZFVP
