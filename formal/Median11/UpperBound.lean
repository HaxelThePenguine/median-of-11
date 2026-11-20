import Median11.Cube
import Median11.Witness

namespace Median11

def passes (net : Network n) (r : Nat) (q : Fin n) (x : Row n Bool) : Bool :=
  (run net x).get q == decide (n - weight x < r)

theorem all_passes_sound (net : Network n) (r : Nat) (q : Fin n)
    (h : (rows n).all (passes net r q) = true) : SelectsBinary net r q := by
  intro x
  simpa [passes] using (List.all_eq_true.mp h x (rows_complete x))

theorem published_size : published.length = 25 := rfl

theorem published_standard : Standard published := by
  unfold Standard published
  simp (config := { maxSteps := 200000 })

/-- Enumerate all choices for the last k wires while retaining the prefix. -/
def extensions (x : Row n Bool) : (k : Nat) → List (Row (n+k) Bool)
  | 0 => [x]
  | k+1 => (extensions x k).flatMap fun y => [y.push false, y.push true]

theorem rows_blocks (n k : Nat) :
    rows (n+k) = (rows n).flatMap (fun x => extensions x k) := by
  induction k with
  | zero => simp [extensions]
  | succ k ih =>
    change (rows (n+k)).flatMap _ = _
    rw [ih, List.flatMap_assoc]
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem published_blocks (x : Row 6 Bool) (hx : x ∈ rows 6) :
    (extensions x 5).all (passes published 6 5) = true := by
  simp only [rows, List.flatMap_cons, List.flatMap_nil, List.nil_append, List.cons_append,
    List.mem_cons, List.not_mem_nil, or_false] at hx
  repeat' rcases hx with hx | hx
  all_goals decide +kernel

theorem published_binary : SelectsBinary published 6 5 := by
  apply all_passes_sound
  change (rows (6+5)).all (passes published 6 5) = true
  rw [rows_blocks]
  apply List.all_eq_true.mpr
  intro x hx
  obtain ⟨initial, hp, hh⟩ := List.mem_flatMap.mp hx
  exact List.all_eq_true.mp (published_blocks initial hp) x hh

theorem published_selects [LE α] [DecidableRel (fun (a b : α) => a ≤ b)]
    (refl : ∀ a : α, a ≤ a)
    (trans : ∀ {a b c : α}, a ≤ b → b ≤ c → a ≤ c)
    (total : ∀ a b : α, a ≤ b ∨ b ≤ a) :
    SelectsRank (α := α) published 6 5 :=
  selectsRank_of_binary refl trans total published_binary

#print axioms published_size
#print axioms published_standard
#print axioms published_binary
#print axioms published_selects

end Median11
