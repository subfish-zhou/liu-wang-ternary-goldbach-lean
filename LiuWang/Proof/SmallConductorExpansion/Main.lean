import LiuWang.Proof.SmallConductorExpansion.Consumer

/-!
# Small-conductor expansion: exhaustive coverage through 32

Every nonprincipal quadratic character at every level `q <= 32` is excluded
from the original closed exceptional real interval, for every `x >= 10`.
No restriction `beta < 1` is hidden: the right half-plane is paid separately.
All actual primitive sources of conductor at most 32 are therefore excluded,
and the frozen R24 ordinary-zero family now has actual conductor at least 33.

The new signed rational certificate permits negative character prefixes.
Prime cyclic classification, exact unit-word covers, and the three-generator
modulus-24 classification supply exhaustive character coverage at these
levels. No floating-point data, zero tables or final-target certificate fields
occur in the proof.

The target of covering every real primitive conductor below 987 remains open
for conductors from 33 through 986. This module does not claim that the fixed
32-term signed certificate suffices for those conductors.
-/
