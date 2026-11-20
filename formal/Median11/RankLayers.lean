import Median11.LowerBound

namespace Median11

theorem weight_increment (x : Row n Bool) (h : weight x < n) :
    ∃ i : Fin n, x.get i = false := by
  have hw := complement_weight x
  have nz : 0 < weight (rowMap Bool.not x) := by omega
  obtain ⟨i, hi, e⟩ := List.getElem_of_mem (List.count_pos_iff.mp nz)
  have hn : i < n := by simpa using hi
  change (rowMap Bool.not x).get ⟨i, hn⟩ = true at e
  exact ⟨⟨i, hn⟩, by simpa using e⟩

theorem extend_ones (x : Row n Bool) (k : Nat) (lo : weight x ≤ k) (hi : k ≤ n) :
    ∃ y : Row n Bool, weight y = k ∧ Pointwise x y := by
  suffices go : ∀ (d : Nat) (z : Row n Bool), weight z + d = k →
      ∃ y : Row n Bool, weight y = k ∧ Pointwise z y from
    go (k-weight x) x (by omega)
  intro d
  induction d with
  | zero => intro z hz; exact ⟨z, by simpa using hz, fun i => by cases z.get i <;> decide⟩
  | succ d ih =>
    intro z hz
    obtain ⟨i, e⟩ := weight_increment z (by omega)
    let z' := z.set i.val true i.isLt
    have inc : weight z' = weight z + 1 := by simp [z', weight_set, e]
    obtain ⟨y, wy, le⟩ := ih z' (by omega)
    refine ⟨y, wy, fun j => ?_⟩
    by_cases same : i = j
    · subst j; rw [e]; cases y.get i <;> decide
    · simpa [z', get_set, same] using le j

theorem restrict_ones (x : Row n Bool) (k : Nat) (lo : k ≤ weight x) :
    ∃ y : Row n Bool, weight y = k ∧ Pointwise y x := by
  have wx := complement_weight x
  obtain ⟨y, wy, le⟩ := extend_ones (rowMap Bool.not x) (n-k) (by omega) (by omega)
  have hw := complement_weight y
  refine ⟨rowMap Bool.not y, by omega, fun i => ?_⟩
  have h := le i
  simp only [get_rowMap] at *
  cases hx : x.get i <;> cases hy : y.get i <;> simp_all [show ¬(true : Bool) ≤ false by decide] <;> decide

def SelectsLayers (net : Network n) (r : Nat) (q : Fin n) : Prop :=
  (∀ x : Row n Bool, weight x = n-r → (run net x).get q = false) ∧
  (∀ x : Row n Bool, weight x = n-r+1 → (run net x).get q = true)

theorem selectsLayers_of_binary {net : Network n} {r : Nat} {q : Fin n}
    (pos : 0 < r) (valid : r ≤ n) (h : SelectsBinary net r q) : SelectsLayers net r q := by
  constructor
  · intro x hw
    rw [h x, hw]
    exact decide_eq_false (by omega)
  · intro x hw
    rw [h x, hw]
    exact decide_eq_true (by omega)

theorem selectsBinary_of_layers {net : Network n} {r : Nat} {q : Fin n}
    (pos : 0 < r) (valid : r ≤ n) (h : SelectsLayers net r q) :
    SelectsBinary net r q := by
  intro x
  by_cases yes : n - weight x < r
  · obtain ⟨y, wy, le⟩ := restrict_ones x (n-r+1) (by omega)
    have below := run_mono net le q
    rw [h.2 y wy] at below
    cases e : (run net x).get q
    · rw [e] at below; exact False.elim ((by decide : ¬(true : Bool) ≤ false) below)
    · simp [yes]
  · obtain ⟨y, wy, le⟩ := extend_ones x (n-r) (by omega) (by omega)
    have below := run_mono net le q
    rw [h.1 y wy] at below
    cases e : (run net x).get q
    · simp [yes]
    · rw [e] at below; exact False.elim ((by decide : ¬(true : Bool) ≤ false) below)

theorem boundary_cover {net : Network n} {r : Nat} {q : Fin n}
    (pos : 0 < r) (valid : r ≤ n) (sel : SelectsBinary net r q)
    {x y : Row n Bool} (le : Pointwise x y)
    (lo : weight x = n-r) (hi : weight y = n-r+1) :
    (run net x).get q = false ∧ (run net y).get q = true ∧
      ∀ j, j ≠ q → (run net x).get j = (run net y).get j := by
  have same := Boundary.edge (layers pos valid sel) (below_rows le) (by simp) (by simp) lo hi
  have layersOk := selectsLayers_of_binary pos valid sel
  refine ⟨layersOk.1 x lo, layersOk.2 y hi, fun j neq => ?_⟩
  simp [layers] at same
  have z := congrArg (fun a : Row n Bool => a.get j) same
  simpa [clear, Ne.symm neq] using z

#print axioms selectsBinary_of_layers
#print axioms boundary_cover

end Median11
