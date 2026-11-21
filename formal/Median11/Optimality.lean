import Median11.OrderedDomain
import Median11.UpperBound
import Median11.LowerBound
import Median11.KernelData.Rank9_4.Result
import Median11.KernelData.Rank9_5.Result

namespace Median11

/-- The structural reduction from the two nine-wire lower bounds. -/
theorem median11_optimal_from_nine (rank4 : Bound 9 4 19) (rank5 : Bound 9 5 19) :
    (∃ net : Network 11, Standard net ∧ SelectsRank (α := Bool) net 6 5 ∧ net.length = 25)
    ∧ (∀ net : Network 11, Standard net → SelectsRank (α := Bool) net 6 5 →
      25 ≤ net.length) := by
  refine ⟨⟨published, published_standard, ?_, published_size⟩, ?_⟩
  · exact published_selects (by decide) (by decide) (by decide)
  · intro net _ selects
    exact standard_lower_from_nine rank4 rank5 net selects

#print axioms median11_optimal_from_nine

/-- The eleven-wire lower bound for either orientation and any fixed output. -/
theorem median11_lower : Bound 11 6 25 :=
  median11_from_nine bound_9_4 bound_9_5

/-- Exact size in the standard-oriented model with output fixed to wire 5. -/
theorem median11_optimal :
    (∃ net : Network 11, Standard net ∧ SelectsRank (α := Bool) net 6 5 ∧ net.length = 25)
    ∧ (∀ net : Network 11, Standard net → SelectsRank (α := Bool) net 6 5 →
      25 ≤ net.length) :=
  median11_optimal_from_nine bound_9_4 bound_9_5

/-- Exact size when the specification quantifies only over inputs in one fixed
decidable total order containing a strict pair. The published witness works
on that same domain, including on rows with ties. -/
theorem median11_optimal_on [LE α] [DecidableRel (fun (a b : α) => a ≤ b)]
    (refl : ∀ x : α, x ≤ x)
    (trans : ∀ {x y z : α}, x ≤ y → y ≤ z → x ≤ z)
    (antisymm : ∀ {x y : α}, x ≤ y → y ≤ x → x = y)
    (total : ∀ x y : α, x ≤ y ∨ y ≤ x)
    (a b : α) (ab : a ≤ b) (ba : ¬ b ≤ a) :
    (Standard published ∧ SelectsRank (α := α) published 6 5 ∧ published.length = 25)
    ∧ (∀ net : Network 11, SelectsRank (α := α) net 6 5 → 25 ≤ net.length) :=
  ⟨⟨published_standard, published_selects refl trans total, published_size⟩,
    fun net h => median11_lower net 5 (selectsBinary_of_orderedRank refl antisymm a b ab ba h)⟩

end Median11
