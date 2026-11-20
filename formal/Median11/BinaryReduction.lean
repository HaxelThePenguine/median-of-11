import Median11.Network

namespace Median11

def weight (x : Row n Bool) : Nat := x.toList.count true

def SelectsBinary (net : Network n) (r : Nat) (q : Fin n) : Prop :=
  ∀ x : Row n Bool, (run net x).get q = decide (n - weight x < r)

/-- The numbers of entries strictly below and at most the output straddle the
one-based rank. Both predicates count with multiplicity, so ties are allowed. -/
def RankValue [LE α] [DecidableRel (fun (a b : α) => a ≤ b)]
    (x : Row n α) (r : Nat) (v : α) : Prop :=
  n - weight (rowMap (fun a => decide (v ≤ a)) x) < r ∧
  r ≤ n - weight (rowMap (fun a => decide (¬ a ≤ v)) x)

def SelectsRank [LE α] [DecidableRel (fun (a b : α) => a ≤ b)]
    (net : Network n) (r : Nat) (q : Fin n) : Prop :=
  ∀ x : Row n α, RankValue x r ((run net x).get q)

private theorem boolMono {p q : Prop} [Decidable p] [Decidable q] (h : p → q) :
    decide p ≤ decide q := by
  by_cases hp : p
  · simp [hp, h hp]
  · rw [decide_eq_false hp]
    cases decide q <;> decide

private theorem boolAntisymm {a b : Bool} : a ≤ b → b ≤ a → a = b := by
  cases a <;> cases b <;> decide

theorem selectsRank_of_binary [LE α] [DecidableRel (fun (a b : α) => a ≤ b)]
    (refl : ∀ a : α, a ≤ a)
    (trans : ∀ {a b c : α}, a ≤ b → b ≤ c → a ≤ c)
    (total : ∀ a b : α, a ≤ b ∨ b ≤ a)
    {net : Network n} {r : Nat} {q : Fin n} (h : SelectsBinary net r q) :
    SelectsRank (α := α) net r q := by
  intro x
  let v := (run net x).get q
  let lower : α → Bool := fun a => decide (v ≤ a)
  let upper : α → Bool := fun a => decide (¬ a ≤ v)
  have lb := congrArg (fun row : Row n Bool => row.get q)
    (run_map lower (fun hab => boolMono (fun h => trans h hab)) total boolAntisymm net x)
  have ub := congrArg (fun row : Row n Bool => row.get q)
    (run_map upper (fun hab => boolMono (fun h hb => h (trans hab hb))) total boolAntisymm net x)
  simp only [get_rowMap] at lb ub
  rw [h (rowMap lower x)] at lb
  rw [h (rowMap upper x)] at ub
  unfold lower at lb
  unfold upper at ub
  change decide (v ≤ v) = _ at lb
  change decide (¬ v ≤ v) = _ at ub
  exact ⟨by simpa [lower, refl v, eq_comm] using lb,
    by simpa [upper, refl v, eq_comm, Nat.not_lt] using ub⟩

theorem weight_le (x : Row n Bool) : weight x ≤ n := by
  simpa [weight] using (List.count_le_length (a := true) (l := x.toList))

theorem selectsBinary_of_boolRank {net : Network n} {r : Nat} {q : Fin n}
    (h : SelectsRank (α := Bool) net r q) :
    SelectsBinary net r q := by
  intro x
  have hx := h x
  unfold RankValue at hx
  cases e : (run net x).get q with
  | false =>
    rw [e] at hx
    have eq : rowMap (fun a : Bool => decide (¬ a ≤ false)) x = x := by
      apply row_ext
      intro i
      rw [get_rowMap]
      cases x.get i <;> rfl
    rw [eq] at hx
    simp [Nat.not_lt.mpr hx.2]
  | true =>
    rw [e] at hx
    have eq : rowMap (fun a : Bool => decide (true ≤ a)) x = x := by
      apply row_ext
      intro i
      rw [get_rowMap]
      cases x.get i <;> rfl
    rw [eq] at hx
    simp [hx.1]

end Median11
