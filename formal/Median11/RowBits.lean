import Median11.Expansion

namespace Median11

/-- A row occupies one bit in a set of binary rows. Wire 0 is its low bit. -/
def rowId (x : Row n Bool) : Nat := (BitVec.ofBoolListLE x.toList).toNat

theorem rowId_testBit (x : Row n Bool) (i : Fin n) : (rowId x).testBit i = x.get i := by
  have valid : i.val < x.toList.length := by simpa using i.isLt
  rw [rowId, BitVec.testBit_toNat, BitVec.getLsb_ofBoolListLE, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem valid]
  simp [Vector.get]

theorem rowId_injective {x y : Row n Bool} (h : rowId x = rowId y) : x = y :=
  row_ext fun i => by rw [← rowId_testBit, h, rowId_testBit]

def rowSet : List (Row n Bool) → Nat
  | [] => 0
  | x :: xs => 2 ^ rowId x ||| rowSet xs

theorem rowSet_mem (x : Row n Bool) (xs : List (Row n Bool)) :
    (rowSet xs).testBit (rowId x) = true ↔ x ∈ xs := by
  induction xs with
  | nil => simp [rowSet]
  | cons y ys ih =>
    have same : rowId y = rowId x ↔ x = y :=
      ⟨fun e => (rowId_injective e).symm, fun e => congrArg rowId e.symm⟩
    simp [rowSet, Nat.testBit_two_pow, ih, same, Bool.or_eq_true]

def gatherDistinct (xs : List (Row n Bool)) : Nat × List (Row n Bool) :=
  match xs with
  | [] => (0, [])
  | x :: rest =>
    let (seen, unique) := gatherDistinct rest
    let id := rowId x
    if seen.testBit id then (seen, unique) else (2 ^ id ||| seen, x :: unique)

theorem gatherDistinct_spec (xs : List (Row n Bool)) :
    (gatherDistinct xs).1 = rowSet xs ∧
    (gatherDistinct xs).2.Nodup ∧
    ∀ x, x ∈ (gatherDistinct xs).2 ↔ x ∈ xs := by
  induction xs with
  | nil => simp [gatherDistinct, rowSet]
  | cons y ys ih =>
    rw [gatherDistinct]
    simp only [ih.1]
    cases e : (rowSet ys).testBit (rowId y) with
    | false =>
      have absent : y ∉ ys := fun hy => by
        have present := (rowSet_mem y ys).mpr hy
        rw [e] at present
        contradiction
      simp [e, ih.2, absent, rowSet]
    | true =>
      have unchanged : 2 ^ rowId y ||| rowSet ys = rowSet ys := by
        apply Nat.eq_of_testBit_eq
        intro i
        by_cases same : rowId y = i
        · subst i
          simp [Nat.testBit_two_pow, e]
        · simp [Nat.testBit_two_pow, same]
      refine ⟨by simp [e, rowSet, unchanged], by simp [e, ih.2.1], ?_⟩
      intro x
      simp only [e, if_true, ih.2.2, List.mem_cons]
      exact ⟨Or.inr, fun h => h.elim (fun f => by subst x; exact (rowSet_mem y ys).mp e) id⟩

end Median11
