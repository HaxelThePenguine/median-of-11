import Std

namespace Median11

theorem length_le_of_nodup_subset [DecidableEq α] {xs ys : List α}
    (unique : xs.Nodup) (incl : xs ⊆ ys) : xs.length ≤ ys.length := by
  induction xs generalizing ys with
  | nil => simp
  | cons a xs ih =>
    have head : a ∈ ys := incl (by simp)
    have nd := List.nodup_cons.mp unique
    have rest : xs ⊆ ys.erase a := by
      intro b hb
      have ne : b ≠ a := by
        intro h
        exact nd.1 (h ▸ hb)
      rw [List.mem_erase_of_ne ne]
      exact incl (by simp [hb])
    have len := ih nd.2 rest
    rw [List.length_erase_of_mem head] at len
    have pos := List.length_pos_of_mem head
    simp only [List.length_cons]
    omega

theorem perm_of_nodup_mem [DecidableEq α] {xs ys : List α}
    (nx : xs.Nodup) (ny : ys.Nodup) (same : ∀ a, a ∈ xs ↔ a ∈ ys) : xs.Perm ys := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => exact List.Perm.nil
    | cons y ys => simpa using (same y).2 (by simp)
  | cons a xs ih =>
    have head := (same a).1 (by simp)
    have expose := List.perm_cons_erase head
    have nd := List.nodup_cons.mp (expose.nodup ny)
    have old := List.nodup_cons.mp nx
    apply List.Perm.trans (List.Perm.cons a (ih old.2 nd.2 ?_)) expose.symm
    intro b
    by_cases e : b = a
    · subst b
      simp [old.1, nd.1]
    · rw [List.mem_erase_of_ne e, ← same b]
      simp [e]

theorem nodup_ofFn {f : Fin n → α} (inj : ∀ a b, f a = f b → a = b) :
    (List.ofFn f).Nodup := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.ofFn_succ, List.nodup_cons, List.mem_ofFn]
    constructor
    · rintro ⟨i, hi⟩
      have neq := congrArg Fin.val (inj i.succ 0 hi)
      simp at neq
    · exact ih (fun a b h => Fin.succ_inj.mp (inj a.succ b.succ h))

theorem map_ofFn (f : Fin n → α) (g : α → β) :
    (List.ofFn f).map g = List.ofFn (g ∘ f) := by
  induction n with
  | zero => simp
  | succ n ih => simp [ih, Function.comp] <;> rfl

end Median11
