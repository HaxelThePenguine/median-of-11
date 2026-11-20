import Median11.CertificateData

/-- Executable diagnostic over the full shipped data. The evaluator result
is not used to construct a theorem or imported as a proof. -/
def main : IO Unit := do
  let mut total := 0
  for (n, r, bound, nodes, passed) in Median11.certificateEvaluations do
    if !passed then throw (IO.userError s!"replay failed at n={n} rank={r}")
    IO.println s!"checked n={n} rank={r} lower={bound} nodes={nodes}"
    total := total + nodes
  IO.println s!"ACCEPT median(11) >= 25; {total} proof nodes"
