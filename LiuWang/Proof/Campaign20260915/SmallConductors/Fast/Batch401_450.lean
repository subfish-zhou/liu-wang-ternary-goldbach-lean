import LiuWang.Proof.Campaign20260915.SmallConductors.Classification
import LiuWang.Proof.SmallConductorExpansion.Continuation.Prime163
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q401.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q403.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q404.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q407.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q408.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q409.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q411.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q412.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q413.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q415.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q417.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q419.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q420.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q421.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q424.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q427.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q428.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q429.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q431.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q433.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q435.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q436.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q437.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q439.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q440.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q443.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q444.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q445.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q447.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q449.Consumer

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
noncomputable section

open LiuWang.Proof.SmallConductorExpansion.Continuation

set_option synthInstance.maxSize 4096

namespace LiuWang.Proof.Campaign20260915.SmallConductors.Fast

theorem range_401_450 {q : ℕ} [NeZero q]
    (hl : 401 ≤ q) (hu : q ≤ 450) (chi : DirichletCharacter ℂ q)
    (hp : chi.IsPrimitive) (hc : chi ≠ 1) (hsq : chi ^ 2 = 1)
    {x beta : ℝ} (hqx : (q : ℝ) ≤ x)
    (hb : 1 - 1 / (9.645908801 * Real.log x) ≤ beta) :
    chi.LFunction (beta : ℂ) ≠ 0 := by
  have ha := primitive_admissible chi hp hsq
  have hall : ∀ k : Fin 451, 401 ≤ k.val → Admissible k.val →
    k.val = 401 ∨
    k.val = 403 ∨
    k.val = 404 ∨
    k.val = 407 ∨
    k.val = 408 ∨
    k.val = 409 ∨
    k.val = 411 ∨
    k.val = 412 ∨
    k.val = 413 ∨
    k.val = 415 ∨
    k.val = 417 ∨
    k.val = 419 ∨
    k.val = 420 ∨
    k.val = 421 ∨
    k.val = 424 ∨
    k.val = 427 ∨
    k.val = 428 ∨
    k.val = 429 ∨
    k.val = 431 ∨
    k.val = 433 ∨
    k.val = 435 ∨
    k.val = 436 ∨
    k.val = 437 ∨
    k.val = 439 ∨
    k.val = 440 ∨
    k.val = 443 ∨
    k.val = 444 ∨
    k.val = 445 ∨
    k.val = 447 ∨
    k.val = 449 := by decide +kernel
  have he := hall ⟨q, by omega⟩ hl ha
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q401.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q403.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q404.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q407.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q408.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q409.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q411.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q412.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q413.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q415.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q417.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q419.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q420.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q421.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q424.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q427.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q428.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q429.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q431.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q433.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q435.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q436.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q437.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q439.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q440.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q443.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q444.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q445.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q447.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q449.original_region chi hp hc hsq hqx hb

#print axioms range_401_450

end LiuWang.Proof.Campaign20260915.SmallConductors.Fast
