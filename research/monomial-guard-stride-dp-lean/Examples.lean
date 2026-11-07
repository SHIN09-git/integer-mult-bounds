import StrideDP.Examples
open StrideDP.Examples

#eval fiveStats
#eval repeatedStats
#eval do
  for (name, ok) in checks do
    IO.println ((if ok then "PASS " else "FAIL ") ++ name)
#guard checks.length = 8
#guard checks.all Prod.snd
