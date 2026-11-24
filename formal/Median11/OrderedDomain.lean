import Median11.BinaryReduction

namespace Median11

/-- Restrict a selection specification on a single ordered type to two of
its values. The strict pair is necessary for a fixed-domain lower bound. -/
theorem selectsBinary_of_orderedRank [LE α] [DecidableRel (fun (a b : α) => a ≤ b)]
    (refl : ∀ a : α, a ≤ a)
    (antisymm : ∀ {a b : α}, a ≤ b → b ≤ a → a = b)
    (a b : α) (ab : a ≤ b) (ba : ¬ b ≤ a)
    {net : Network n} {r : Nat} {q : Fin n} (h : SelectsRank (α := α) net r q) :
    SelectsBinary net r q := by
  let f : Bool → α := fun t => if t then b else a
  have ord (u v : Bool) : f u ≤ f v ↔ u ≤ v := by
    cases u <;> cases v <;> simp [f, refl, ab, ba] <;> decide
  apply selectsBinary_of_boolRank
  intro x
  have hx := h (rowMap f x)
  have comm := run_map f (fun hle => (ord _ _).2 hle)
    (fun (u v : Bool) => by cases u <;> cases v <;> decide) antisymm net x
  unfold RankValue at hx ⊢
  rw [← comm, get_rowMap] at hx
  let v := (run net x).get q
  have low : rowMap (fun u => decide (f v ≤ u)) (rowMap f x) =
      rowMap (fun u => decide (v ≤ u)) x := by
    apply row_ext
    intro i
    simp only [get_rowMap, ord]
  have high : rowMap (fun u => decide (¬ u ≤ f v)) (rowMap f x) =
      rowMap (fun u => decide (¬ u ≤ v)) x := by
    apply row_ext
    intro i
    simp only [get_rowMap, ord]
  rwa [low, high] at hx

end Median11
