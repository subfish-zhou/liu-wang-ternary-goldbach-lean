import LiuWang.Proof.Campaign20260915.ZetaValidation.Zeta16BlockData

namespace LiuWang.Proof.Campaign20260915.ZetaValidation

#eval do
  for b in List.range 8 do
    IO.println ((List.range 8).map fun j => ⌊1000 * (power16Center (b * 8 + j + 1)).1⌋)
  IO.println ((List.range 64).map fun j =>
    ⌊1000 * (∑ n ∈ Finset.range (j + 1), (power16Center (n + 1)).1)⌋).min?
#eval (⌊1000 * (power16Center 64).1⌋, ⌊1000 * (power16Center 64).2⌋)

end LiuWang.Proof.Campaign20260915.ZetaValidation
