import Median11.UpperBound
import Median11.LowerBound

namespace Median11

/-- A proof over the model in the paper. Its nine-wire certificate obligations
are explicit arguments until the relevant concrete replays are kernel-checked. -/
theorem median11_optimal_from_nine (rank4 : Bound 9 4 19) (rank5 : Bound 9 5 19) :
    (∃ net : Network 11, Standard net ∧ SelectsRank (α := Bool) net 6 5 ∧ net.length = 25)
    ∧ (∀ net : Network 11, Standard net → SelectsRank (α := Bool) net 6 5 →
      25 ≤ net.length) := by
  refine ⟨⟨published, published_standard, ?_, published_size⟩, ?_⟩
  · exact published_selects (by decide) (by decide) (by decide)
  · intro net _ selects
    exact standard_lower_from_nine rank4 rank5 net selects

#print axioms median11_optimal_from_nine

end Median11
