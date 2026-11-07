import BucketDP.Examples
open BucketDP BucketDP.Examples

#eval do
  for (name,e) in [("five",solutionEvents five),("repeated",solutionEvents repeated),("collision",solutionEvents collision)] do
    IO.println s!"{name} rows={e.rows} labels={e.retained} types={e.types} cells={e.cells} comparisons={e.comparisons} bucketVisits={e.bucketTests} pops={e.pops} realLabels={e.realNodes} gates={e.gates}"
  for (name,ok) in checks do
    IO.println ((if ok then "PASS " else "FAIL ") ++ name)
#guard checks.length = 8
#guard checks.all Prod.snd
