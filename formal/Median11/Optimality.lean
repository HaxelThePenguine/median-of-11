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

end Median11
