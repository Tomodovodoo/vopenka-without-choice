import PalomarBridge.ZFDictionary
import ZFVP.SetTheory.FunctionComposition

/-! Exact agreement of the independent set operations with Foundation.
These equalities justify the shared definitions in the independent VP dictionary. -/

namespace PalomarBridge
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {M : Type u} [SetStructure M] [Nonempty M] [M↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

local notation "mem" => (fun x y : M => x ∈ y)

theorem setValue_eq (P : M → Prop) (s : M) (hs : ∀ x, x ∈ s ↔ P x) :
    Coding.setValue mem P = s := by
  apply mem_ext
  intro x
  exact (Classical.epsilon_spec (show ∃ t : M, ∀ x, x ∈ t ↔ P x from ⟨s, hs⟩) x).trans (hs x).symm

@[simp] theorem coding_empty : Coding.empty mem = (∅ : M) := by
  apply setValue_eq
  simp

@[simp] theorem coding_unordered (x y : M) : Coding.unordered mem x y = ({x, y} : M) := by
  apply setValue_eq
  simp

@[simp] theorem coding_pair (x y : M) : Coding.pair mem x y = ⟨x, y⟩ₖ := by
  simp [Coding.pair, kpair]

@[simp] theorem coding_union (a : M) : Coding.union mem a = ⋃ˢ a := by
  apply setValue_eq
  simp [mem_sUnion_iff]

@[simp] theorem coding_inter (a : M) : Coding.inter mem a = ⋂ˢ a := by
  apply setValue_eq
  simp [mem_sInter_iff, isNonempty_def]

@[simp] theorem coding_first (p : M) : Coding.first mem p = kpair.π₁ p := by
  simp [Coding.first, kpair.π₁]

@[simp] theorem coding_second (p : M) : Coding.second mem p = kpair.π₂ p := by
  unfold Coding.second
  rw [coding_union]
  congr 1
  apply setValue_eq
  simp

@[simp] theorem coding_succ (x : M) : Coding.succ mem x = succ x := by
  apply setValue_eq
  simp [mem_succ_iff]

@[simp] theorem coding_numeral (n : Nat) : Coding.numeral mem n = (n : M) := by
  induction n with
  | zero => exact coding_empty
  | succ n hn => simpa only [Coding.numeral, coding_succ, hn] using (show succ (n : M) = ((n + 1 : Nat) : M) from rfl)

@[simp] theorem coding_domain (f : M) : Coding.domain mem f = domain f := by
  apply setValue_eq
  simp [mem_domain_iff]

@[simp] theorem coding_range (f : M) : Coding.range mem f = range f := by
  apply setValue_eq
  simp [mem_range_iff]

@[simp] theorem coding_value (f x : M) : Coding.value mem f x = f ‘ x := by
  apply setValue_eq
  intro z
  simp only [value, mem_sep_iff, coding_pair]
  constructor
  · exact And.right
  · rintro ⟨y, hzy, hxy⟩
    exact ⟨mem_sUnion_iff.mpr ⟨y, mem_range_of_kpair_mem hxy, hzy⟩, y, hzy, hxy⟩

@[simp] theorem coding_functions (Y X : M) : Coding.functions mem Y X = Y ^ X := by
  apply setValue_eq
  simp [mem_function_iff, subset_def, mem_prod_iff]

@[simp] theorem coding_isFunction (f : M) : Coding.IsFunction mem f ↔ IsFunction f := by
  simp [Coding.IsFunction, isFunction_iff]

@[simp] theorem coding_omega : Coding.omega mem = (ω : M) := by
  apply setValue_eq
  simp [mem_ω_iff_mem_all_inductive, Coding.Inductive, IsInductive]

@[simp] theorem coding_compose (f g : M) : Coding.compose mem f g = compose f g := by
  apply setValue_eq
  simp only [mem_compose_iff, coding_pair]
  intro p
  constructor
  · rintro ⟨x, y, z, hf, hg, he⟩
    exact ⟨x, y, z, he, hf, hg⟩
  · rintro ⟨x, y, z, he, hf, hg⟩
    exact ⟨x, y, z, hf, hg, he⟩

@[simp] theorem coding_restrict (f A : M) : Coding.restrict mem f A = f ↾ A := by
  apply setValue_eq
  simp only [mem_restrict_iff, coding_pair]
  intro p
  constructor
  · rintro ⟨hpf, x, hx, y, he⟩
    exact ⟨x, hx, y, he, hpf⟩
  · rintro ⟨x, hx, y, he, hpf⟩
    exact ⟨hpf, x, hx, y, he⟩

end PalomarBridge

