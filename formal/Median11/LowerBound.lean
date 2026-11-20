import Median11.ExtremePath

namespace Median11

/-- Every fixed oriented network selecting this rank has at least this size,
regardless of the chosen output. -/
def Bound (n r size : Nat) : Prop :=
  ∀ (net : Network n) (q : Fin n), SelectsBinary net r q → size ≤ net.length

def frameAt (i : Fin (n+1)) : Frame n :=
  (initialFrame n).trans (swapIso 0 i)

@[simp] theorem frameAt_sentinel (i : Fin (n+1)) : (frameAt i).forward none = i := by
  simp [frameAt, initialFrame, Relabel.trans, swapIso, swapIndex]

theorem bound_dual {n r size : Nat} (pos : 0 < r) (valid : r ≤ n)
    (h : Bound n r size) : Bound n (n+1-r) size := by
  intro net q sel
  have copy := selects_dual (show n+1-r ≤ n by omega) sel
  have rank : n+1-(n+1-r) = r := by omega
  rw [rank] at copy
  simpa using h (net.map dualGate) q copy

theorem deletion_size_bound {n r budget : Nat} {net : Network (n+1)} {q i : Fin (n+1)}
    (pos : 0 < r) (valid : r ≤ n+1) (sel : SelectsBinary net r q)
    (v : Bool) (keeps : if v then r ≤ n else 1 < r) (b : Nat) (small : Bound n (if v then r else r-1) b)
    (cost : net.length ≤ budget) : (trace net i v).2 + b ≤ budget := by
  obtain ⟨j, h⟩ := deletion_rank net (frameAt i) v q r pos valid keeps sel
  have low := small _ j h
  have sum := deletion_count net (frameAt i) v
  rw [encounters_trace, frameAt_sentinel] at sum
  omega

theorem deletion_step_bound {n r bmin bmax : Nat} (lo : 1 < r) (hi : r ≤ n)
    (w : Nat) (layer : w = n+1-r ∨ w = n+1-r+1) (ones : 4 ≤ w) (zeros : w+4 ≤ n+1)
    (minBound : Bound n (r-1) bmin) (maxBound : Bound n r bmax) :
    Bound (n+1) r (3 + min bmin bmax) := by
  intro net q sel
  obtain ⟨i,v,h⟩ := three_comparisons (by omega) (by omega) sel w layer ones zeros
  cases v
  · have bound := deletion_size_bound (by omega) (by omega) sel false lo bmin minBound (Nat.le_refl net.length) (i := i)
    have m := Nat.min_le_left bmin bmax
    omega
  · have bound := deletion_size_bound (by omega) (by omega) sel true hi bmax maxBound (Nat.le_refl net.length) (i := i)
    have m := Nat.min_le_right bmin bmax
    omega

/-- The concrete reduction. The two nine-wire bound hypotheses are discharged
by the external certificate replay in the paper, not by this theorem. -/
theorem median11_from_nine (rank4 : Bound 9 4 19) (rank5 : Bound 9 5 19) :
    Bound 11 6 25 := by
  have rank6 : Bound 9 6 19 := bound_dual (r := 4) (by decide) (by decide) rank4
  have left : Bound 10 5 22 := deletion_step_bound
    (r := 5) (by decide) (by decide) 5 (by decide) (by decide) (by decide) rank4 rank5
  have right : Bound 10 6 22 := deletion_step_bound
    (r := 6) (by decide) (by decide) 5 (by decide) (by decide) (by decide) rank5 rank6
  exact deletion_step_bound
    (r := 6) (by decide) (by decide) 5 (by decide) (by decide) (by decide) left right

theorem standard_lower_from_nine (rank4 : Bound 9 4 19) (rank5 : Bound 9 5 19)
    (net : Network 11) (h : SelectsRank (α := Bool) net 6 5) : 25 ≤ net.length :=
  median11_from_nine rank4 rank5 net 5 (selectsBinary_of_boolRank h)

#print axioms deletion_rank
#print axioms deletion_step_bound
#print axioms median11_from_nine
#print axioms standard_lower_from_nine

end Median11
