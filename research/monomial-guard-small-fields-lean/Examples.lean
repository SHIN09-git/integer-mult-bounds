import SmallFields.Examples
open SmallFields SmallFields.Examples

#eval do
  IO.println s!"F3 zero-total histograms checked against the general DP: {cases3.length}"
  IO.println s!"F5 zero-total histograms checked against the general DP: {cases5.length}"
  IO.println s!"Z([1,1,3]) over F5 = {direct5 [1,1,3]}"
  for (name,ok) in checks do
    IO.println ((if ok then "PASS " else "FAIL ") ++ name)
#guard checks.length = 8
#guard checks.all Prod.snd
