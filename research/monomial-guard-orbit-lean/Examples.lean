import OrbitGuard.Examples
open OrbitGuard OrbitGuard.Examples

#eval do
  IO.println s!"Normalized two-row inputs: {tinyCases.length} of {3^6}"
  if let some (w,e) := solveFixed five then
    IO.println s!"Five-row optimum. Additions (dst,src,coefficient mod 3) = {describe w}"
    IO.println s!"Final row order (zero-based) = {List.ofFn (fun i => (e i).val)}"
  for (name,ok) in checks do
    IO.println ((if ok then "PASS " else "FAIL ") ++ name)
#guard checks.length = 8
#guard checks.all Prod.snd
