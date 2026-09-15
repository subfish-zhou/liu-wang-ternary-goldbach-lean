import LiuWang.Proof.CharacterExpansion.Main

set_option autoImplicit false

noncomputable section

open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.CharacterExpansion AnalyticNumberTheory.LargeSieve
open scoped BigOperators

section Finite

variable {N a q : Nat} [NeZero q] (η α : Real) (χ : Character q)

example (n : Nat) :
    ZMod.stdAddChar (n : ZMod q) = charReal ((n : Real) / (q : Real)) :=
  stdAddChar_nat n

example (n : Nat) :
    ZMod.stdAddChar ((a : ZMod q) * (n : ZMod q)) =
      charReal ((n : Real) * rationalCenter a q) :=
  rational_phase a n

example :
    G a χ = ∑ l : ZMod q,
      star (χ l) * charReal ((a : Real) * (l.val : Real) / (q : Real)) :=
  G_eq_conjugate_sum a χ

example :
    G a χ = gaussSum χ⁻¹ (ZMod.stdAddChar.mulShift (a : ZMod q)) :=
  G_eq_inverse_gauss a χ

example :
    (∑ χ : Character q, G a χ * twistedS N η χ) =
      ∑ χ : Character q, gaussSum χ (ZMod.stdAddChar.mulShift (a : ZMod q)) *
        twistedS N η χ⁻¹ :=
  gauss_twistedS_reindex N a η

example (n : ZMod q) :
    (∑ χ : Character q, G a χ * χ n) =
      if IsUnit n then (q.totient : Complex) * ZMod.stdAddChar ((a : ZMod q) * n)
      else 0 :=
  character_kernel a n

example :
    S N (rationalCenter a q + η) =
      (q.totient : Complex)⁻¹ * (∑ χ : Character q, G a χ * twistedS N η χ) +
        nonCoprimeError N q (rationalCenter a q + η) :=
  S_character_expansion N a η

example :
    ‖nonCoprimeError N q α‖ ≤
      ∑ n ∈ (windowFinset N).filter (fun n => ¬ Nat.Coprime n q),
        ArithmeticFunction.vonMangoldt n :=
  norm_nonCoprimeError_le_mass N q α

example (hN : 0 < N) :
    (∑ n ∈ (windowFinset N).filter (fun n => ¬ Nat.Coprime n q),
      ArithmeticFunction.vonMangoldt n) ≤
    ∑ n ∈ (Finset.Icc 1 N).filter (fun n => ¬ Nat.Coprime n q),
      ArithmeticFunction.vonMangoldt n :=
  window_nonCoprime_mass_le_prefix hN q

example (hN : 0 < N) :
    ‖nonCoprimeError N q α‖ ≤ Real.log q * sourceL N / Real.log 2 :=
  norm_nonCoprimeError_le_log hN (NeZero.pos q) α

example (hN : Real.exp 2000 ≤ (N : Real)) (hqP : (q : Real) ≤ sourceP1 N) :
    Real.log q ≤ sourceL N :=
  log_modulus_le_sourceL hN (NeZero.pos q) hqP

example (hN : Real.exp 2000 ≤ (N : Real)) (hqP : (q : Real) ≤ sourceP1 N) :
    ‖nonCoprimeError N q α‖ ≤ sourceL N ^ 2 / Real.log 2 :=
  norm_nonCoprimeError_le_source hN (NeZero.pos q) hqP α

example (hN : Real.exp 2000 ≤ (N : Real)) (hi : sourceIndex a q)
    (hqP : (q : Real) ≤ sourceP1 N) :
    S N (rationalCenter a q + η) =
      (q.totient : Complex)⁻¹ * (∑ χ : Character q, G a χ * twistedS N η χ) +
        nonCoprimeError N q (rationalCenter a q + η) ∧
    ‖nonCoprimeError N q (rationalCenter a q + η)‖ ≤ sourceL N ^ 2 / Real.log 2 :=
  S_character_expansion_source hN hi hqP η

example (hN : Real.exp 2000 ≤ (N : Real)) (hi : sourceIndex a q)
    (hqP : (q : Real) ≤ sourceP1 N) (hα : α = rationalCenter a q + η) :
    (∑ n ∈ windowFinset N, (ArithmeticFunction.vonMangoldt n : Complex) *
      charReal ((n : Real) * α)) =
        (q.totient : Complex)⁻¹ * (∑ χ : Character q, G a χ * twistedS N η χ) +
          nonCoprimeError N q α := by
  subst α
  simpa only [S, LiuWang.Fourier.liuWangExpSum, LiuWang.Fourier.indexedExpSum,
    Int.cast_natCast] using (source_contract hN hi hqP η).1

example (hN : Real.exp 2000 ≤ (N : Real)) (hi : sourceIndex a q)
    (hqP : (q : Real) ≤ sourceP1 N) :
    ‖S N (rationalCenter a q + η) -
      (q.totient : Complex)⁻¹ * (∑ χ : Character q, G a χ * twistedS N η χ)‖ ≤
      sourceL N ^ 2 / Real.log 2 := by
  obtain ⟨hexp, herr, _⟩ := source_contract hN hi hqP η
  rw [hexp, add_sub_cancel_left]
  exact herr

end Finite

section Induction

variable {q m n p a : Nat} [NeZero q] [NeZero m] [NeZero n]
    (χ : Character q)

example :
    gaussSum χ ZMod.stdAddChar =
      ∑ n ∈ Finset.range q, χ (n : ZMod q) * charReal ((n : Real) / (q : Real)) :=
  gaussSum_eq_range χ

example (hd : q ∣ m) (hqm : q < m) :
    (∑ x : ZMod m, χ (ZMod.castHom hd (ZMod q) x) * ZMod.stdAddChar x) = 0 :=
  sum_pullback_stdAddChar_eq_zero hd hqm χ

example (hp : p.Prime) (n : Nat) :
    DirichletCharacter.changeLevel (dvd_mul_left q p) χ (n : ZMod (p * q)) =
      χ (n : ZMod q) - if p ∣ n then χ (n : ZMod q) else 0 :=
  changeLevel_prime_apply hp χ n

example (hp : 0 < p) (f : Nat → Complex) :
    (∑ n ∈ Finset.range (p * q), if p ∣ n then f n else 0) =
      ∑ n ∈ Finset.range q, f (p * n) :=
  sum_range_multiples hp f

example [NeZero (p * q)] (hp : p.Prime) :
    gaussSum (DirichletCharacter.changeLevel (dvd_mul_left q p) χ) ZMod.stdAddChar =
      -χ (p : ZMod q) * gaussSum χ ZMod.stdAddChar :=
  gaussSum_changeLevel_prime hp χ

example [NeZero (p * q)] (hp : p.Prime) :
    ‖gaussSum (DirichletCharacter.changeLevel (dvd_mul_left q p) χ) ZMod.stdAddChar‖ ≤
      ‖gaussSum χ ZMod.stdAddChar‖ :=
  norm_gaussSum_changeLevel_prime hp χ

example (h : m = n) (hm : q ∣ m) (hn : q ∣ n) :
    gaussSum (DirichletCharacter.changeLevel hm χ) ZMod.stdAddChar =
      gaussSum (DirichletCharacter.changeLevel hn χ) ZMod.stdAddChar :=
  gaussSum_changeLevel_congr h hm hn χ

example (k : Nat) [NeZero (k * q)] :
    ‖gaussSum (DirichletCharacter.changeLevel (dvd_mul_left q k) χ) ZMod.stdAddChar‖ ≤
      ‖gaussSum χ ZMod.stdAddChar‖ :=
  norm_gaussSum_changeLevel_mul k q χ

example (hd : q ∣ m) :
    ‖gaussSum (DirichletCharacter.changeLevel hd χ) ZMod.stdAddChar‖ ≤
      ‖gaussSum χ ZMod.stdAddChar‖ :=
  norm_gaussSum_changeLevel hd χ

example : primitiveGaussAddChar q = ZMod.stdAddChar :=
  primitiveGaussAddChar_eq_std

example (hχ : χ.IsPrimitive) : ‖gaussSum χ ZMod.stdAddChar‖ = Real.sqrt q :=
  norm_gaussSum_primitive χ hχ

example : ‖gaussSum χ ZMod.stdAddChar‖ ≤ Real.sqrt χ.conductor :=
  norm_gaussSum_le_sqrt_conductor χ

example (ha : Nat.Coprime a q) :
    G a χ = χ (a : ZMod q) * gaussSum χ⁻¹ ZMod.stdAddChar :=
  G_eq_char_mul_gaussSum ha χ

example (ha : Nat.Coprime a q) : ‖G a χ‖ ≤ Real.sqrt χ.conductor :=
  norm_G_le_sqrt_conductor ha χ

example (hd : q ∣ m) (ha : Nat.Coprime a m) (hχ : χ.IsPrimitive) :
    ‖G a (DirichletCharacter.changeLevel hd χ)‖ ≤ Real.sqrt q :=
  norm_G_induced_le_sqrt hd ha χ hχ

end Induction

section Endpoints

example (χ : Character 1) (x : ZMod 1) : χ x = 1 :=
  character_level_one_apply χ x

example (N : Nat) (α : Real) : nonCoprimeError N 1 α = 0 :=
  nonCoprimeError_one N α

example (a : Nat) (χ : Character 1) : G a χ = 1 := G_one a χ

example (N : Nat) (η : Real) (χ : Character 1) : twistedS N η χ = S N η :=
  twistedS_one N η χ

example (N : Nat) (η : Real) :
    S N (1 + η) = S N η ∧ nonCoprimeError N 1 (1 + η) = 0 :=
  S_character_expansion_one N η

example {N : Nat} (hN : Real.exp 2000 ≤ (N : Real)) (η : Real) :
    ‖nonCoprimeError N 1 (1 + η)‖ ≤ sourceL N ^ 2 / Real.log 2 := by
  have h := source_contract hN (by norm_num [sourceIndex] : sourceIndex 1 1)
    (by simpa only [Nat.cast_one] using
      (one_le_sourceP hN).trans (sourceP_le_sourceP1 hN)) η
  simpa [rationalCenter] using h.2.1

example {q a : Nat} [NeZero q] (ha : Nat.Coprime a q) :
    ‖G a (1 : Character q)‖ ≤ 1 := by
  simpa [DirichletCharacter.conductor_one] using
    norm_G_le_sqrt_conductor ha (1 : Character q)

example : gaussSum (1 : Character 4) ZMod.stdAddChar = 0 := by
  have h := gaussSum_changeLevel_prime (q := 2) Nat.prime_two (1 : Character 2)
  have hz : (1 : Character 2) (2 : ZMod 2) = 0 := by
    apply MulChar.map_nonunit
    have hcop : ¬ Nat.Coprime 2 2 := by decide
    exact (ZMod.isUnit_iff_coprime 2 2).not.mpr hcop
  rw [map_one] at h
  change gaussSum (1 : Character 4) ZMod.stdAddChar =
    -((1 : Character 2) (2 : ZMod 2)) * gaussSum (1 : Character 2) ZMod.stdAddChar at h
  rw [hz, neg_zero, zero_mul] at h
  exact h

example : 1 ∈ windowFinset 1000 := by
  simp

example : 1 ∉ windowFinset 1001 := by
  simp

example (N : Nat) : N ∈ windowFinset N := by
  simp
  omega

end Endpoints
