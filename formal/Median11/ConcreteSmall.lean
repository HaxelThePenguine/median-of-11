import Median11.SmallData

namespace Median11

set_option maxRecDepth 20000
set_option maxHeartbeats 0

theorem bound_2_1 : Bound 2 1 1 :=
  verify_replay_sound (budget := 0) (by decide) (by decide) (Or.inl rfl) (Or.inl rfl)
    data2_1 (by decide +kernel)

theorem bound_3_1 : Bound 3 1 2 :=
  verify_replay_sound (budget := 1) (by decide) (by decide) (Or.inl rfl)
    (Or.inr ⟨by decide, bound_2_1⟩) data3_1 (by decide +kernel)

theorem bound_3_2 : Bound 3 2 3 :=
  verify_replay_sound (budget := 2) (by decide) (by decide) (Or.inr ⟨by decide, bound_2_1⟩)
    (Or.inr ⟨by decide, bound_dual (r := 1) (by decide) (by decide) bound_2_1⟩)
    data3_2 (by decide +kernel)

theorem bound_4_1 : Bound 4 1 3 :=
  verify_replay_sound (budget := 2) (by decide) (by decide) (Or.inl rfl)
    (Or.inr ⟨by decide, bound_3_1⟩) data4_1 (by decide +kernel)

theorem bound_4_2 : Bound 4 2 5 :=
  verify_replay_sound (budget := 4) (by decide) (by decide) (Or.inr ⟨by decide, bound_3_1⟩)
    (Or.inr ⟨by decide, bound_3_2⟩) data4_2 (by decide +kernel)

theorem bound_5_1 : Bound 5 1 4 :=
  verify_replay_sound (budget := 3) (by decide) (by decide) (Or.inl rfl)
    (Or.inr ⟨by decide, bound_4_1⟩) data5_1 (by decide +kernel)

theorem bound_5_2 : Bound 5 2 7 :=
  verify_replay_sound (budget := 6) (by decide) (by decide) (Or.inr ⟨by decide, bound_4_1⟩)
    (Or.inr ⟨by decide, bound_4_2⟩) data5_2 (by decide +kernel)

theorem bound_5_3 : Bound 5 3 7 :=
  verify_replay_sound (budget := 6) (by decide) (by decide) (Or.inr ⟨by decide, bound_4_2⟩)
    (Or.inr ⟨by decide, bound_dual (r := 2) (by decide) (by decide) bound_4_2⟩)
    data5_3 (by decide +kernel)

theorem bound_6_1 : Bound 6 1 5 :=
  verify_replay_sound (budget := 4) (by decide) (by decide) (Or.inl rfl)
    (Or.inr ⟨by decide, bound_5_1⟩) data6_1 (by decide +kernel)

theorem bound_6_2 : Bound 6 2 9 :=
  verify_replay_sound (budget := 8) (by decide) (by decide) (Or.inr ⟨by decide, bound_5_1⟩)
    (Or.inr ⟨by decide, bound_5_2⟩) data6_2 (by decide +kernel)

theorem bound_6_3 : Bound 6 3 10 :=
  verify_replay_sound (budget := 9) (by decide) (by decide) (Or.inr ⟨by decide, bound_5_2⟩)
    (Or.inr ⟨by decide, bound_5_3⟩) data6_3 (by decide +kernel)

theorem bound_7_1 : Bound 7 1 6 :=
  verify_replay_sound (budget := 5) (by decide) (by decide) (Or.inl rfl)
    (Or.inr ⟨by decide, bound_6_1⟩) data7_1 (by decide +kernel)

theorem bound_7_2 : Bound 7 2 11 :=
  verify_replay_sound (budget := 10) (by decide) (by decide) (Or.inr ⟨by decide, bound_6_1⟩)
    (Or.inr ⟨by decide, bound_6_2⟩) data7_2 (by decide +kernel)

theorem bound_7_3 : Bound 7 3 12 :=
  verify_replay_sound (budget := 11) (by decide) (by decide) (Or.inr ⟨by decide, bound_6_2⟩)
    (Or.inr ⟨by decide, bound_6_3⟩) data7_3 (by decide +kernel)

theorem bound_7_4 : Bound 7 4 13 :=
  verify_replay_sound (budget := 12) (by decide) (by decide) (Or.inr ⟨by decide, bound_6_3⟩)
    (Or.inr ⟨by decide, bound_dual (r := 3) (by decide) (by decide) bound_6_3⟩)
    data7_4 (by decide +kernel)

theorem bound_8_1 : Bound 8 1 7 :=
  verify_replay_sound (budget := 6) (by decide) (by decide) (Or.inl rfl)
    (Or.inr ⟨by decide, bound_7_1⟩) data8_1 (by decide +kernel)

theorem bound_8_2 : Bound 8 2 13 :=
  verify_replay_sound (budget := 12) (by decide) (by decide) (Or.inr ⟨by decide, bound_7_1⟩)
    (Or.inr ⟨by decide, bound_7_2⟩) data8_2 (by decide +kernel)

theorem bound_8_3 : Bound 8 3 14 :=
  verify_replay_sound (budget := 13) (by decide) (by decide) (Or.inr ⟨by decide, bound_7_2⟩)
    (Or.inr ⟨by decide, bound_7_3⟩) data8_3 (by decide +kernel)

theorem bound_9_1 : Bound 9 1 8 :=
  verify_replay_sound (budget := 7) (by decide) (by decide) (Or.inl rfl)
    (Or.inr ⟨by decide, bound_8_1⟩) data9_1 (by decide +kernel)

#print axioms bound_6_3

end Median11
