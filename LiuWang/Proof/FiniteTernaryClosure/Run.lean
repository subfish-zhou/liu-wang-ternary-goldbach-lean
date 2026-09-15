import LiuWang.Proof.FiniteTernaryClosure.Regression

set_option autoImplicit false

open LiuWang.Proof.FiniteTernaryClosure

private def expect (label : String) (actual expected : Bool) : IO Unit := do
  IO.println s!"CHECK {label}: actual={actual} expected={expected}"
  unless actual == expected do
    throw (IO.userError s!"certificate regression failed: {label}")

def main : IO Unit := do
  let cs := regressionCertificates
  expect "complete odd interval 9..1000" (checkInterval 9 1000 cs) true
  expect "496 rows" (cs.length == 496) true
  expect "exact indices, no sampling"
    (cs.map Certificate.n == (List.range 496).map (fun k => 9 + 2 * k)) true
  for c in cs do
    unless checkCertificate c do
      throw (IO.userError s!"invalid row: {repr c}")
    IO.println s!"CERT n={c.n} p={c.p} q={c.q} r={c.r} accepted=true"
  expect "missing first" (checkInterval 9 1000 (cs.drop 1)) false
  expect "missing middle" (checkInterval 9 1000 (cs.take 250 ++ cs.drop 251)) false
  expect "missing last" (checkInterval 9 1000 (cs.take 495)) false
  expect "duplicate row" (checkInterval 9 1000 (cs.take 1 ++ cs)) false
  expect "reversed rows" (checkInterval 9 1000 cs.reverse) false
  expect "excess row" (checkInterval 9 1000 (cs ++ [⟨9, 3, 3, 3⟩])) false
  expect "even lower endpoint" (checkInterval 8 1000 cs) false
  expect "misincluded 1" (checkInterval 1 1000 cs) false
  expect "misincluded 5" (checkInterval 5 1000 cs) false
  expect "misincluded 7" (checkInterval 7 1000 cs) false
  expect "7=2+2+3" (checkCertificate ⟨7, 2, 2, 3⟩) false
  expect "one is not prime" (checkCertificate ⟨9, 1, 3, 5⟩) false
  expect "composite coordinate" (checkCertificate ⟨15, 3, 3, 9⟩) false
  expect "wrong sum" (checkCertificate ⟨11, 3, 3, 3⟩) false
  expect "repeated odd primes" (checkCertificate ⟨9, 3, 3, 3⟩) true
  IO.println "PASS: all 496 odd targets in 9..1000; no analytic claim."
