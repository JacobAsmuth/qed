/- Browser entry: the plain-Html keyed-list baseline, run through the verified diff path. -/
import Examples.Bench.ListDiff
import Qed.Driver

def main : IO Unit := Qed.run BenchListDiff.diffApp
