import LiuWang.Proof.Campaign20260915.RSMediumRange.GridWalk

set_option autoImplicit false

namespace LiuWang.Proof.Campaign20260915.RSMediumRange

def unpackRows : ℕ → ℕ → ℕ → ℕ → List MediumRow
  | _, 0, _, _ => []
  | previous, len + 1, rows, factors =>
      let p := rows % 2 ^ 27
      let e := rows / 2 ^ 27 % 2 ^ 5
      let lo := rows / 2 ^ 32 % 2 ^ 51
      let hi := rows / 2 ^ 83 % 2 ^ 51
      let root := rows / 2 ^ 134 % 2 ^ 34
      let gapScale := 2 ^ (16 * (p - previous - 1))
      ⟨p, e, lo, hi, root, factors % gapScale⟩ ::
        unpackRows p len (rows / 2 ^ 168) (factors / gapScale)

end LiuWang.Proof.Campaign20260915.RSMediumRange
