import Median11.BinaryReduction

namespace Median11

def rows : (n : Nat) → List (Row n Bool)
  | 0 => [#v[]]
  | n+1 => (rows n).flatMap fun x => [x.push false, x.push true]

theorem push_pop_last (x : Row (n+1) Bool) :
    x.pop.push (x.get ⟨n, by omega⟩) = x := by
  apply Vector.ext
  intro i hi
  by_cases h : i < n
  · simp [Vector.getElem_push, h]
  · have eq : i = n := by omega
    subst i
    simp [Vector.getElem_push, Vector.get]

theorem rows_complete (x : Row n Bool) : x ∈ rows n := by
  induction n with
  | zero =>
    simp [rows]
  | succ n ih =>
    rw [rows, List.mem_flatMap]
    refine ⟨x.pop, ih x.pop, ?_⟩
    have hp := push_pop_last x
    cases h : x.get ⟨n, by omega⟩ <;> simp_all

end Median11
