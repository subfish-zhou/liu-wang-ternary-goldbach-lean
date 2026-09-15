import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Cover

set_option autoImplicit false

namespace LiuWang.Proof.Campaign20260915.SmallConductors.Fast

def KernelEntries (q d start : ℕ) : List ℤ → Prop
  | [] => True
  | v :: vs =>
    (start % d = 1 % d → start.Coprime q → v = 1) ∧
      KernelEntries q d (start + 1) vs

instance (q d start : ℕ) (values : List ℤ) :
    Decidable (KernelEntries q d start values) := by
  induction values generalizing start with
  | nil => exact isTrue True.intro
  | cons v vs ih =>
    let : Decidable (KernelEntries q d (start + 1) vs) := ih _
    unfold KernelEntries
    infer_instance

theorem kernelEntries_getD {q d start : ℕ} {values : List ℤ}
    (h : KernelEntries q d start values) :
    ∀ i < values.length, (start + i) % d = 1 % d →
      (start + i).Coprime q → values.getD i 0 = 1 := by
  induction values generalizing start with
  | nil => simp
  | cons v vs ih =>
    intro i hi
    cases i with
    | zero => simpa using h.1
    | succ i =>
      simpa [List.getD_eq_getElem?_getD, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using ih h.2 i (by simpa using hi)

theorem factorsThrough_of_kernel_entries {q d : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (values : List ℤ) (hd : d ∣ q)
    (ht : ∀ z : ZMod q, chi z = (values.getD z.val 0 : ℂ))
    (hlen : values.length = q) (h : KernelEntries q d 0 values) :
    chi.FactorsThrough d := by
  apply (DirichletCharacter.factorsThrough_iff_ker_unitsMap hd).mpr
  intro u hu
  rw [MonoidHom.mem_ker, Units.ext_iff, ZMod.unitsMap_val, ← ZMod.natCast_val,
    Units.val_one, ← Nat.cast_one, ZMod.natCast_eq_natCast_iff'] at hu
  have hc : u.val.val.Coprime q :=
    (ZMod.isUnit_iff_coprime _ _).mp (by simp)
  have hv := kernelEntries_getD h u.val.val (by simpa only [hlen] using u.val.val_lt)
  simp only [Nat.zero_add] at hv
  rw [MonoidHom.mem_ker, Units.ext_iff, MulChar.coe_toUnitHom, Units.val_one,
    ht, hv hu hc, Int.cast_one]

theorem not_primitive_of_kernel_entries {q d : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (values : List ℤ) (hd : d ∣ q) (hlt : d < q)
    (ht : ∀ z : ZMod q, chi z = (values.getD z.val 0 : ℂ))
    (hlen : values.length = q) (h : KernelEntries q d 0 values) :
    ¬chi.IsPrimitive := by
  intro hp
  have hc : chi.conductor ≤ d :=
    Nat.sInf_le (factorsThrough_of_kernel_entries chi values hd ht hlen h)
  rw [hp] at hc
  omega

end LiuWang.Proof.Campaign20260915.SmallConductors.Fast
