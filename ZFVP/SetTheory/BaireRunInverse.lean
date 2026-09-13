import ZFVP.SetTheory.BaireRunCoding
import ZFVP.SetTheory.CantorRunPositions

/-! The run parser is an inverse on the dense G-delta of infinitely many ones. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def cantorRunDecodeFormula : SetTheorySemisentence 2 :=
  f“a x. ∀ p, p ∈ a ↔ ∃ n ∈ !isω, p = !kpair.dfn n
    (!naturalDifferenceFormula (!cantorRunStartFormula x n)
      (!cantorNextOneFormula x (!cantorRunStartFormula x n)))”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def cantorRunDecode (x : V) : V :=
  definableGraph (ω : V) (fun n ↦ naturalDifference (cantorRunStart x n)
    (cantorNextOne x (cantorRunStart x n))) (by definability)

theorem mem_cantorRunDecode_iff (x p : V) : p ∈ cantorRunDecode x ↔
    ∃ n ∈ (ω : V), p = ⟨n, naturalDifference (cantorRunStart x n)
      (cantorNextOne x (cantorRunStart x n))⟩ₖ := mem_definableGraph_iff _ _ _ _

instance cantorRunDecodeFormula_defined :
    ℒₛₑₜ-function₁[V] cantorRunDecode via cantorRunDecodeFormula :=
  ⟨fun v ↦ by simp [cantorRunDecodeFormula, mem_ext_iff (y := cantorRunDecode _),
    mem_cantorRunDecode_iff]⟩

instance cantorRunDecode_definable : ℒₛₑₜ-function₁[V] cantorRunDecode :=
  cantorRunDecodeFormula_defined.to_definable

theorem cantorRunDecode_value (x : V) {n : V} (hn : n ∈ (ω : V)) :
    (cantorRunDecode x) ‘ n = naturalDifference (cantorRunStart x n)
      (cantorNextOne x (cantorRunStart x n)) := value_definableGraph _ _ _ hn

theorem cantorRunDecode_mem {x : V} (hx : x ∈ cantorInfiniteOnes V) :
    cantorRunDecode x ∈ baireSpace V := by
  apply definableGraph_mem_function_of_mapsTo
  intro n hn
  have hl := cantorRunStart_mem hx hn
  exact (naturalDifference_spec hl (cantorNextOne_mem hx hl) (cantorNextOne_ge hx hl)).1

theorem binaryAppendRun_reconstruct {x l : V} (hx : x ∈ cantorInfiniteOnes V) (hl : l ∈ (ω : V)) :
    binaryAppendRun (x ↾ l) (naturalDifference l (cantorNextOne x l)) =
      x ↾ (succ (cantorNextOne x l)) := by
  have hxc := ((mem_cantorInfiniteOnes_iff x).mp hx).1
  have hk := cantorNextOne_mem hx hl
  have hks := ω_succ_closed hk
  have hd := naturalDifference_spec hl hk (cantorNextOne_ge hx hl)
  have hs := function_restrict_mem hxc (IsTransitive.transitive _ hl)
  have hsb := restrict_mem_binarySequences hxc hl
  have ht := function_restrict_mem hxc (IsTransitive.transitive _ hks)
  have : IsFunction x := IsFunction.of_mem hxc
  have : IsFunction (x ↾ l) := IsFunction.of_mem hs
  have : IsFunction (x ↾ (succ (cantorNextOne x l))) := IsFunction.of_mem ht
  have : IsFunction (binaryAppendRun (x ↾ l) (naturalDifference l (cantorNextOne x l))) :=
    IsFunction.of_mem (binaryAppendRun_mem_function hs)
  apply functions_eq_of_domain_values (by
    rw [binaryAppendRun_domain hs, hd.2, domain_eq_of_mem_function ht])
  intro i hi
  rw [binaryAppendRun_domain hs, hd.2] at hi
  have hiω := IsTransitive.ω.transitive _ hks _ hi
  rw [value_restrict (by rw [domain_eq_of_mem_function hxc]; exact hiω) hi]
  rcases mem_succ_iff.mp hi with rfl | hi
  · have he := binaryAppendRun_separator (a := naturalDifference l (cantorNextOne x l)) hsb
    rw [domain_eq_of_mem_function hs, hd.2] at he
    exact he.trans (cantorNextOne_value hx hl).symm
  · by_cases hil : i ∈ l
    · have hid : i ∈ domain (x ↾ l) := by rw [domain_eq_of_mem_function hs]; exact hil
      rw [value_eq_of_subset_function (binaryAppendRun_extends hsb hd.1) hid]
      exact value_restrict (by rw [domain_eq_of_mem_function hxc]; exact hiω) hil
    · have : IsOrdinal l := IsOrdinal.of_mem hl
      have : IsOrdinal i := IsOrdinal.of_mem hiω
      have hli : l ⊆ i := by
        rcases IsOrdinal.mem_trichotomy l i with hlt | rfl | hgt
        · exact IsOrdinal.subset_iff.mpr (Or.inr hlt)
        · exact subset_refl _
        · exact (hil hgt).elim
      rw [binaryAppendRun_zero hsb (by simpa [domain_eq_of_mem_function hs, hd.2] using hi)
        (by simpa [domain_eq_of_mem_function hs] using hil), cantorNextOne_before_zero hx hl hli hi]

theorem baireRunPrefix_decode {x n : V} (hx : x ∈ cantorInfiniteOnes V) (hn : n ∈ (ω : V)) :
    baireRunPrefix (cantorRunDecode x) n = x ↾ (cantorRunStart x n) := by
  apply naturalNumber_induction
    (fun n ↦ baireRunPrefix (cantorRunDecode x) n = x ↾ (cantorRunStart x n))
    (by definability) ?_ ?_ n hn
  · rw [baireRunPrefix_zero, cantorRunStart_zero]
    simp [zero_def]
  · intro n hn ih
    rw [baireRunPrefix_succ _ hn, ih, cantorRunDecode_value x hn, cantorRunStart_succ x hn]
    exact binaryAppendRun_reconstruct hx (cantorRunStart_mem hx hn)

theorem baireRunCode_decode {x : V} (hx : x ∈ cantorInfiniteOnes V) :
    baireRunCode (cantorRunDecode x) = x := by
  have ha := cantorRunDecode_mem hx
  have hxc := ((mem_cantorInfiniteOnes_iff x).mp hx).1
  have : IsFunction x := IsFunction.of_mem hxc
  have : IsFunction (baireRunCode (cantorRunDecode x)) := baireRunCode_isFunction ha
  apply functions_eq_of_domain_values (by rw [baireRunCode_domain ha, domain_eq_of_mem_function hxc])
  intro i hi
  rw [baireRunCode_domain ha] at hi
  have hn := ω_succ_closed hi
  have his : i ∈ cantorRunStart x (succ i) :=
    cantorRunStart_length_bound hx hn i (mem_succ_self i)
  have hs := function_restrict_mem hxc (IsTransitive.transitive _ (cantorRunStart_mem hx hn))
  have hip : i ∈ domain (baireRunPrefix (cantorRunDecode x) (succ i)) := by
    rw [baireRunPrefix_decode hx hn, domain_eq_of_mem_function hs]
    exact his
  rw [baireRunCode_value_of_prefix ha hn hip, baireRunPrefix_decode hx hn]
  exact value_restrict (by rw [domain_eq_of_mem_function hxc]; exact hi) his

theorem cantorRunDecode_code {a : V} (ha : a ∈ baireSpace V) :
    cantorRunDecode (baireRunCode a) = a := by
  apply baireRunCode_injective (cantorRunDecode_mem (baireRunCode_infiniteOnes ha)) ha
  exact baireRunCode_decode (baireRunCode_infiniteOnes ha)

theorem baireRunCode_surjective {x : V} (hx : x ∈ cantorInfiniteOnes V) :
    ∃ a ∈ baireSpace V, baireRunCode a = x :=
  ⟨cantorRunDecode x, cantorRunDecode_mem hx, baireRunCode_decode hx⟩

end ZFVP
