import LiuWang.Proof.EffectiveLValue.OddClassFormula
import LiuWang.Proof.EffectiveLValue.PellLowerBound
import LiuWang.Proof.EffectiveLValue.AllParityLowerBound

/-!
# Effective lower bound for real primitive characters

The original cutoff `r >= 987` supports the full bound `L(1, chi) >= pi / sqrt r`
for both parities. The odd branch uses an integral character moment; the even
branch uses the original cyclotomic product and its proved integral Pell
coefficients. No class-number formula or conductor-shape premise is required.

The older Gauss-field and Pell infrastructure remains available. Its separate
field-discriminant and Dedekind-zeta factorization route is not claimed closed.
-/
