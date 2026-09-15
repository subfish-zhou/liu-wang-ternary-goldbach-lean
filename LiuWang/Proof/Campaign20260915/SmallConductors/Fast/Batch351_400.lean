import LiuWang.Proof.Campaign20260915.SmallConductors.Classification
import LiuWang.Proof.SmallConductorExpansion.Continuation.Prime163
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q353.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q355.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q356.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q357.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q359.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q364.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q365.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q367.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q371.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q372.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q373.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q376.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q377.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q379.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q380.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q381.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q383.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q385.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q388.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q389.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q391.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q393.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q395.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q397.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q399.Consumer

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
noncomputable section

open LiuWang.Proof.SmallConductorExpansion.Continuation

set_option synthInstance.maxSize 4096

namespace LiuWang.Proof.Campaign20260915.SmallConductors.Fast

theorem range_351_400 {q : ℕ} [NeZero q]
    (hl : 351 ≤ q) (hu : q ≤ 400) (chi : DirichletCharacter ℂ q)
    (hp : chi.IsPrimitive) (hc : chi ≠ 1) (hsq : chi ^ 2 = 1)
    {x beta : ℝ} (hqx : (q : ℝ) ≤ x)
    (hb : 1 - 1 / (9.645908801 * Real.log x) ≤ beta) :
    chi.LFunction (beta : ℂ) ≠ 0 := by
  have ha := primitive_admissible chi hp hsq
  have hall : ∀ k : Fin 401, 351 ≤ k.val → Admissible k.val →
    k.val = 353 ∨
    k.val = 355 ∨
    k.val = 356 ∨
    k.val = 357 ∨
    k.val = 359 ∨
    k.val = 364 ∨
    k.val = 365 ∨
    k.val = 367 ∨
    k.val = 371 ∨
    k.val = 372 ∨
    k.val = 373 ∨
    k.val = 376 ∨
    k.val = 377 ∨
    k.val = 379 ∨
    k.val = 380 ∨
    k.val = 381 ∨
    k.val = 383 ∨
    k.val = 385 ∨
    k.val = 388 ∨
    k.val = 389 ∨
    k.val = 391 ∨
    k.val = 393 ∨
    k.val = 395 ∨
    k.val = 397 ∨
    k.val = 399 := by decide +kernel
  have he := hall ⟨q, by omega⟩ hl ha
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q353.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q355.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q356.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q357.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q359.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q364.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q365.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q367.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q371.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q372.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q373.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q376.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q377.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q379.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q380.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q381.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q383.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q385.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q388.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q389.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q391.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q393.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q395.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q397.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q399.original_region chi hp hc hsq hqx hb

#print axioms range_351_400

end LiuWang.Proof.Campaign20260915.SmallConductors.Fast
