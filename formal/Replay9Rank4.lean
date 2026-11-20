import Median11.CertificateData

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem nine_rank_four_replay :
    Median11.verifyReplay 9 4 18 14 16 Median11.data9_4 = true := by
  decide +kernel

#print axioms nine_rank_four_replay
