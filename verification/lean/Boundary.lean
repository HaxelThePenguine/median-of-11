import Std

/- The selected output is stored separately from all other outputs.
   Only monotonicity, conservation and the prescribed values on two layers enter. -/
namespace Boundary

abbrev Bits := List Bool
abbrev wt (x : Bits) := x.count true

def Below : Bits → Bits → Prop
  | [], [] => True
  | a :: x, b :: y => (a = false ∨ b = true) ∧ Below x y
  | _, _ => False

theorem belowRefl (x : Bits) : Below x x := by
  induction x with
  | nil => trivial
  | cons b x ih => cases b <;> simp [Below, ih]

theorem liftPrefix (p : Bits) {x y : Bits} (h : Below x y) :
    Below (p ++ x) (p ++ y) := by
  induction p with
  | nil => exact h
  | cons b p ih => cases b <;> simp [Below, ih]

theorem massUnique {x y : Bits} (h : Below x y) :
    wt x ≤ wt y ∧ (wt x = wt y → x = y) := by
  induction x generalizing y with
  | nil => cases y <;> simp_all [Below]
  | cons a x ih =>
    cases y with
    | nil => contradiction
    | cons b y =>
      obtain ⟨hle, heq⟩ := ih h.2
      have hab := h.1
      cases a <;> cases b <;> simp_all [wt, List.count_cons] <;> omega

structure OutputMap (n w : Nat) where
  bit : Bits → Bool
  rest : Bits → Bits
  mono : ∀ {x y}, x.length = n → Below x y → Below (rest x) (rest y)
  mass : ∀ x, x.length = n → wt x = wt (rest x) + (if bit x then 1 else 0)
  lo : ∀ x, x.length = n → wt x = w → bit x = false
  hi : ∀ x, x.length = n → wt x = w+1 → bit x = true

theorem edge {n w} (F : OutputMap n w) {x y} (h : Below x y)
    (nx : x.length = n) (ny : y.length = n) (hx : wt x = w) (hy : wt y = w+1) : F.rest x = F.rest y := by
  apply (massUnique (F.mono nx h)).2
  have a := F.mass x nx
  have b := F.mass y ny
  rw [F.lo x nx hx] at a
  rw [F.hi y ny hy] at b
  simp at a b
  omega

private theorem adjacent {n w} (F : OutputMap n w) (p t : Bits)
    (len : p.length + (t.length+2) = n)
    (h : wt (p ++ true::false::t) = w ∨ wt (p ++ true::false::t) = w+1) :
    F.rest (p ++ true::false::t) = F.rest (p ++ false::true::t) := by
  have refl := belowRefl t
  simp [wt, List.count_append, List.count_cons] at h
  rcases h with lo | hi
  · have left := @edge n w F (p ++ true::false::t) (p ++ true::true::t)
    have right := @edge n w F (p ++ false::true::t) (p ++ true::true::t)
    apply Eq.trans (left (liftPrefix p (by simp [Below, refl])) (by simpa using len) (by simpa using len) (by simpa [wt, List.count_cons] using lo) ?_)
    · symm
      apply right (liftPrefix p (by simp [Below, refl])) (by simpa using len) (by simpa using len) <;> simp [wt, List.count_cons] <;> omega
    · simp [wt, List.count_cons]; omega
  · have left := @edge n w F (p ++ false::false::t) (p ++ true::false::t)
    have right := @edge n w F (p ++ false::false::t) (p ++ false::true::t)
    have low : wt (p ++ false::false::t) = w := by simp [wt, List.count_cons]; omega
    apply Eq.trans (left (liftPrefix p (by simp [Below, refl])) (by simpa using len) (by simpa using len) low ?_).symm
    · apply right (liftPrefix p (by simp [Below, refl])) (by simpa using len) (by simpa using len) low
      simpa [wt, List.count_cons] using hi
    · simpa [wt, List.count_cons] using hi

theorem permRest {n w} (F : OutputMap n w) {x y : Bits} (h : x.Perm y) (p : Bits)
    (len : (p ++ x).length = n)
    (hw : wt (p ++ x) = w ∨ wt (p ++ x) = w+1) :
    F.rest (p ++ x) = F.rest (p ++ y) := by
  induction h generalizing p with
  | nil => rfl
  | cons b h ih => simpa using ih (p ++ [b]) (by simpa using len) (by simpa using hw)
  | swap a b t =>
    cases a <;> cases b
    · rfl
    · exact adjacent F p t (by simpa using len) hw
    · symm; apply adjacent F p t (by simpa using len)
      simpa [wt, List.count_cons] using hw
    · rfl
  | trans h₁ h₂ ih₁ ih₂ =>
    apply Eq.trans (ih₁ p len hw) (ih₂ p (by simpa [List.length_append, h₁.length_eq] using len) ?_)
    have eq := (List.perm_iff_count.mp h₁) true
    simpa [wt, List.count_append, eq] using hw

private theorem countBoth (x : Bits) : x.count false + x.count true = x.length := by
  induction x with
  | nil => rfl
  | cons b x ih => cases b <;> simp_all [List.count_cons] <;> omega

theorem rigidity {n w} (F : OutputMap n w) {x y : Bits}
    (nx : x.length = n) (len : x.length = y.length) (weight : wt x = wt y)
    (h : wt x = w ∨ wt x = w+1) :
    (F.bit x, F.rest x) = (F.bit y, F.rest y) := by
  have perm : x.Perm y := by
    apply List.perm_iff_count.mpr
    intro b
    cases b
    · have hx := countBoth x
      have hy := countBoth y
      change x.count true = y.count true at weight
      omega
    · exact weight
  have rest := permRest F perm [] (by simpa using nx) (by simpa using h)
  simp only [List.nil_append] at rest
  rcases h with lo | hi
  · rw [F.lo x nx lo, F.lo y (len ▸ nx) (weight ▸ lo), rest]
  · rw [F.hi x nx hi, F.hi y (len ▸ nx) (weight ▸ hi), rest]

#print axioms rigidity
#print axioms edge
end Boundary
