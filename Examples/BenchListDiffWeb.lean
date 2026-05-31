/- WASM entry: the plain-Html keyed-list baseline, run through the verified diff path. -/
import Examples.BenchListDiff
import Qed.Driver

def main : IO Unit := Qed.run BenchListDiff.diffApp
