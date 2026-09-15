import LiuWang.Proof.Campaign20260915.SmallConductors.Classification
import LiuWang.Proof.SmallConductorExpansion.Continuation.Prime163
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q151.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q152.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q155.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q156.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q157.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q159.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q161.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q164.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q165.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q167.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q168.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q172.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q173.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q177.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q179.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q181.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q183.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q184.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q185.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q187.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q188.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q191.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q193.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q195.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q197.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q199.Consumer

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
noncomputable section

open LiuWang.Proof.SmallConductorExpansion.Continuation

namespace LiuWang.Proof.Campaign20260915.SmallConductors.Fast

theorem range_151_200 {q : ℕ} [NeZero q]
    (hl : 151 ≤ q) (hu : q ≤ 200) (chi : DirichletCharacter ℂ q)
    (hp : chi.IsPrimitive) (hc : chi ≠ 1) (hsq : chi ^ 2 = 1)
    {x beta : ℝ} (hqx : (q : ℝ) ≤ x)
    (hb : 1 - 1 / (9.645908801 * Real.log x) ≤ beta) :
    chi.LFunction (beta : ℂ) ≠ 0 := by
  have ha := primitive_admissible chi hp hsq
  have hall : ∀ k : Fin 201, 151 ≤ k.val → Admissible k.val →
    k.val = 151 ∨
    k.val = 152 ∨
    k.val = 155 ∨
    k.val = 156 ∨
    k.val = 157 ∨
    k.val = 159 ∨
    k.val = 161 ∨
    k.val = 163 ∨
    k.val = 164 ∨
    k.val = 165 ∨
    k.val = 167 ∨
    k.val = 168 ∨
    k.val = 172 ∨
    k.val = 173 ∨
    k.val = 177 ∨
    k.val = 179 ∨
    k.val = 181 ∨
    k.val = 183 ∨
    k.val = 184 ∨
    k.val = 185 ∨
    k.val = 187 ∨
    k.val = 188 ∨
    k.val = 191 ∨
    k.val = 193 ∨
    k.val = 195 ∨
    k.val = 197 ∨
    k.val = 199 := by decide +kernel
  have he := hall ⟨q, by omega⟩ hl ha
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q151.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q152.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q155.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q156.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q157.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q159.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q161.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.SmallConductorExpansion.Continuation.quadratic_163_original_region chi hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q164.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q165.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q167.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q168.original_region chi hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q172.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q173.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q177.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q179.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q181.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q183.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q184.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q185.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q187.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q188.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q191.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q193.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q195.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q197.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q199.original_region chi hp hc hsq hqx hb

#print axioms range_151_200

end LiuWang.Proof.Campaign20260915.SmallConductors.Fast
