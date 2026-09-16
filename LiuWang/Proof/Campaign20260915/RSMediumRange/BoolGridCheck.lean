import LiuWang.Proof.Campaign20260915.RSMediumRange.PackedRows

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace LiuWang.Proof.Campaign20260915.RSMediumRange

def checkFactors : ℕ → ℕ → ℕ → Bool
  | _, 0, code => code.beq 0
  | n, len + 1, code =>
      (2 : ℕ).ble (code % 65536) && (code % 65536).blt n &&
        (n % (code % 65536)).beq 0 &&
        checkFactors (n + 1) len (code / 65536)

theorem factors_of_check {n len code : ℕ} (h : checkFactors n len code = true) :
    packedCompositeRun n len code := by
  induction len generalizing n code with
  | zero => simpa [checkFactors, packedCompositeRun] using h
  | succ len ih =>
    simp only [checkFactors, Bool.and_eq_true] at h
    refine ⟨?_, ?_, ?_, ih h.2⟩ <;> simp_all

def checkCell (s : MediumState) (b root : ℕ) : Bool :=
  s.thetaLo.ble s.thetaHi &&
  s.thetaHi.blt (s.p * fixedScale) &&
  ((b * fixedScale - s.thetaLo) ^ 2).blt (4 * b * fixedScale ^ 2) &&
  (b * 1000000 ^ 2).ble (root ^ 2) &&
  (s.eulerHi * 100000000 * root).blt
    (178107239 * (s.logLo * root + 2 * 1000000 * fixedScale))

theorem cell_of_check {s : MediumState} {b root : ℕ}
    (h : checkCell s b root = true) : CellCheck s b root := by
  simpa [checkCell, CellCheck, Bool.and_eq_true, and_assoc] using h

def checkGridStep (s : MediumState) (r : MediumRow) : Bool :=
  s.p.blt r.p && r.p.ble 100000000 &&
  (1024 : ℕ).ble (r.p / 2 ^ r.k) && (r.p / 2 ^ r.k).blt 2048 &&
  (gridRowLo r.p r.k).beq r.logLo && (gridRowHi r.p r.k).beq r.logHi &&
  checkFactors (s.p + 1) (r.p - s.p - 1) r.gap && checkCell s r.p r.root

theorem step_of_check {s : MediumState} {r : MediumRow}
    (h : checkGridStep s r = true) : GridStepCheck s r := by
  simp only [checkGridStep, Bool.and_eq_true] at h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, factors_of_check h.1.2, cell_of_check h.2⟩
  all_goals simp_all

def checkGrid : MediumState → List MediumRow → Bool
  | _, [] => true
  | s, r :: rs => checkGridStep s r && checkGrid (nextState s r) rs

theorem gridWalk_of_check {s : MediumState} {rs : List MediumRow}
    (h : checkGrid s rs = true) : GridWalk s rs := by
  induction rs generalizing s with
  | nil => trivial
  | cons r rs ih =>
    simp only [checkGrid, Bool.and_eq_true] at h
    exact ⟨step_of_check h.1, ih h.2⟩

theorem gridWalk_prime_range {s : MediumState} {rs : List MediumRow}
    (hs : 16000 ≤ s.p) (hc : GridWalk s rs) :
    ∀ r ∈ rs, 2 ≤ r.p ∧ r.p ≤ 100000000 := by
  induction rs generalizing s with
  | nil => simp
  | cons r rs ih =>
    intro q hq
    have hsp := hc.1.1
    simp only [List.mem_cons] at hq
    rcases hq with rfl | hq
    · exact ⟨by omega, hc.1.2.1⟩
    · exact ih (by change 16000 ≤ r.p; omega) hc.2 q hq

theorem certifiedChunk_of_boolGrid {s t : MediumState} {rs : List MediumRow}
    (hs : 16000 ≤ s.p) (he : rs.foldl nextState s = t)
    (hc : checkGrid s rs = true)
    (hprime : Nat.Coprime (rs.map MediumRow.p).prod factorialBase) :
    CertifiedChunk s t :=
  certifiedChunk_of_gridWalk hs he (gridWalk_of_check hc)
    (gridWalk_prime_range hs (gridWalk_of_check hc)) hprime

#print axioms certifiedChunk_of_boolGrid

end LiuWang.Proof.Campaign20260915.RSMediumRange
