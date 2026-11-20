import Median11.CertificateData

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem nine_rank_five_replay :
    Median11.verifyReplay 9 5 18 16 16 Median11.data9_5 = true := by
  decide +kernel

#print axioms nine_rank_five_replay
