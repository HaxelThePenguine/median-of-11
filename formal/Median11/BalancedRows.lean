import Median11.Deletion

namespace Median11

def wires (n : Nat) : List (Fin n) := List.ofFn id

@[simp] theorem mem_wires (i : Fin n) : i ∈ wires n :=
  List.mem_ofFn.mpr ⟨i,rfl⟩

theorem nodup_wires (n : Nat) : (wires n).Nodup :=
  nodup_ofFn (fun _ _ h => h)

private theorem indicator_weight (xs : List (Fin n)) (nd : xs.Nodup) :
    weight (Vector.ofFn fun i => decide (i ∈ xs)) = xs.length := by
  let supporting := (wires n).filter (fun i => decide (i ∈ xs))
  have perm : supporting.Perm xs := perm_of_nodup_mem
    ((nodup_wires n).filter _) nd (by simp [supporting])
  rw [← perm.length_eq]
  simp only [weight, Vector.toList_ofFn, supporting, List.count_eq_countP, List.countP_eq_length_filter]
  rw [show List.ofFn (fun i : Fin n => decide (i ∈ xs)) =
      (wires n).map (fun i => decide (i ∈ xs)) by rw [wires, map_ofFn]; rfl]
  simp [List.filter_map, Function.comp] <;> rfl

/-- Each support can be held uniformly false or true on the same layer,
provided the layer has at least that many of each bit. -/
theorem uniform_on_layer (xs : List (Fin n)) (k : Nat) (b : Bool)
    (enough : xs.length ≤ k) (room : k + xs.length ≤ n) :
    ∃ x : Row n Bool, weight x = k ∧ ∀ i ∈ xs, x.get i = b := by
  let free := (wires n).filter (fun i => decide (i ∉ xs))
  let busy := (wires n).filter (fun i => decide (i ∈ xs))
  have subset : busy ⊆ xs := by intro a ha; simpa [busy] using ha
  have cb := length_le_of_nodup_subset ((nodup_wires n).filter _) subset
  change busy.length ≤ xs.length at cb
  have both : free.length + busy.length = n := by
    have len := List.length_eq_countP_add_countP (fun i : Fin n => decide (i ∉ xs)) (l := wires n)
    simp [wires, List.countP_eq_length_filter] at len
    simpa [free, busy, wires, decide_not] using len.symm
  have capacity : k ≤ free.length := by omega
  let size := if b then n-k else k
  have cap : size ≤ free.length := by cases b <;> simp [size] <;> omega
  let subset := free.take size
  have nd := ((nodup_wires n).filter (fun i => decide (i ∉ xs))).sublist (List.take_sublist size free)
  let y : Row n Bool := Vector.ofFn fun i => decide (i ∈ subset)
  have yw : weight y = size := (indicator_weight _ nd).trans (List.length_take_of_le cap)
  have off (i : Fin n) (hi : i ∈ xs) : y.get i = false := by
    have no : i ∉ subset := by
      intro h
      have hf := List.mem_of_mem_take h
      simpa [free, hi] using hf
    simpa [y, Vector.get] using no
  cases b with
  | false => exact ⟨y, yw, off⟩
  | true =>
    refine ⟨rowMap Bool.not y, ?_, ?_⟩
    · have hw := complement_weight y
      simp [yw, size] at hw
      omega
    · intro i hi
      simp [off i hi]

end Median11
