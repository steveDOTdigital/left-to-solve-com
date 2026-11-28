import OMAReductions.R_Erdos821_erdos_821_variants_lichtman_R1
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Lichtman counts smooth shifted primes with multiplicity by factoring
their predecessors. Two divisors determine an ordered three-factor
representation, so the standard fourth divisor moment controls the
loss on passing to distinct primes. A fixed power of the logarithm is
then smaller than the reserved power of x.
The rational smoothness exponent is strictly within Lichtman's range. -/

open Filter
open scoped BigOperators

namespace OMA.R_Erdos821_erdos_821_variants_lichtman_R1_H1_R1

/-- The chosen rational exponent lies above the analytic cutoff. -/
theorem lichtman_cutoff_lt :
    15 / (32 * Real.sqrt (Real.exp 1)) < (2843115 : ℝ) / 10000000 := by
  let b : ℝ := 2843115 / 10000000
  have hb : 0 < b := by norm_num [b]
  have hs : 0 < Real.sqrt (Real.exp 1) := Real.sqrt_pos.2 (Real.exp_pos _)
  have hsq : (15 / (32 * b)) ^ 2 < Real.exp 1 := by
    exact (show (15 / (32 * b)) ^ 2 < (2.7182818283 : ℝ) by norm_num [b]).trans
      Real.exp_one_gt_d9
  have h : 15 / (32 * b) < Real.sqrt (Real.exp 1) := by
    apply (sq_lt_sq₀ (by positivity) hs.le).mp
    simpa only [Real.sq_sqrt (Real.exp_pos 1).le] using hsq
  have hh := (div_lt_iff₀ (show 0 < 32 * b by positivity)).mp h
  change 15 / (32 * Real.sqrt (Real.exp 1)) < b
  apply (div_lt_iff₀ (show 0 < 32 * Real.sqrt (Real.exp 1) by positivity)).mpr
  calc
    15 < Real.sqrt (Real.exp 1) * (32 * b) := hh
    _ = _ := by ring

private theorem card_image_moment {α : Type*} {A T : Finset α} (f : α → ℕ) (x : ℕ)
    (hAT : A ⊆ T) (hfx : ∀ t ∈ A, f t ≤ x) :
    (A.card : ℝ) ^ 2 ≤ ((A.image f).card : ℝ) *
      ∑ p ∈ Finset.range (x + 1), ((T.filter (fun t => f t = p)).card : ℝ) ^ 2 := by
  let w (p : ℕ) : ℝ := (A.filter (fun t => f t = p)).card
  have hCard : (A.card : ℝ) = ∑ p ∈ A.image f, w p := by
    dsimp only [w]
    exact_mod_cast Finset.card_eq_sum_card_image f A
  have hCauchy := Finset.sum_mul_sq_le_sq_mul_sq (A.image f) (fun _ => (1 : ℝ)) w
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hCauchy
  have hsub : A.image f ⊆ Finset.range (x + 1) := by
    intro p hp
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hp
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (hfx t ht))
  have hsum :
      ∑ p ∈ A.image f, (w p) ^ 2 ≤
        ∑ p ∈ Finset.range (x + 1), ((T.filter (fun t => f t = p)).card : ℝ) ^ 2 := by
    calc
      _ ≤ ∑ p ∈ Finset.range (x + 1), (w p) ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => sq_nonneg (w p))
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro p _
        have hle := Finset.card_le_card
          (Finset.filter_subset_filter (fun t => f t = p) hAT)
        apply pow_le_pow_left₀ (by dsimp [w]; positivity) _ 2
        dsimp only [w]
        exact_mod_cast hle
  rw [hCard]
  exact hCauchy.trans (mul_le_mul_of_nonneg_left hsum (by positivity))

private theorem triple_fiber_le_divisors_sq (x p : ℕ) :
    let T := (Finset.Icc 1 x) ×ˢ ((Finset.Icc 1 x) ×ˢ (Finset.Icc 1 x))
    (T.filter (fun t => t.1 * t.2.1 * t.2.2 + 1 = p)).card ≤
      (p - 1).divisors.card ^ 2 := by
  intro T
  let F := T.filter (fun t => t.1 * t.2.1 * t.2.2 + 1 = p)
  have hpos {t : ℕ × ℕ × ℕ} (ht : t ∈ F) : 0 < t.1 ∧ 0 < t.2.1 ∧ 0 < t.2.2 := by
    have h := Finset.mem_product.mp (Finset.mem_filter.mp ht).1
    have hh := Finset.mem_product.mp h.2
    exact ⟨(Finset.mem_Icc.mp h.1).1, (Finset.mem_Icc.mp hh.1).1, (Finset.mem_Icc.mp hh.2).1⟩
  change F.card ≤ _
  rw [pow_two, ← Finset.card_product]
  refine Finset.card_le_card_of_injOn (fun t => (t.1, t.2.1)) ?_ ?_
  · intro t ht
    have ht' := Finset.mem_coe.mp ht
    obtain ⟨ha, hb, hc⟩ := hpos ht'
    have hprod := (Finset.mem_filter.mp ht').2
    have he : t.1 * t.2.1 * t.2.2 = p - 1 := by omega
    have hp : p - 1 ≠ 0 := by
      rw [← he]
      exact (Nat.mul_pos (Nat.mul_pos ha hb) hc).ne'
    refine Finset.mem_coe.mpr (Finset.mem_product.mpr ⟨?_, ?_⟩)
    · exact Nat.mem_divisors.mpr ⟨⟨t.2.1 * t.2.2, by rw [← he]; ring⟩, hp⟩
    · exact Nat.mem_divisors.mpr ⟨⟨t.1 * t.2.2, by rw [← he]; ring⟩, hp⟩
  · intro u hu v hv he
    have ha : u.1 = v.1 := congrArg (fun p : ℕ × ℕ => p.1) he
    have hb : u.2.1 = v.2.1 := congrArg (fun p : ℕ × ℕ => p.2) he
    have hu' := Finset.mem_coe.mp hu
    have hv' := Finset.mem_coe.mp hv
    have hpU := (Finset.mem_filter.mp hu').2
    have hpV := (Finset.mem_filter.mp hv').2
    rw [← ha, ← hb] at hpV
    have hmul : u.1 * u.2.1 * u.2.2 = u.1 * u.2.1 * v.2.2 := by omega
    have hne : u.1 * u.2.1 ≠ 0 := (Nat.mul_pos (hpos hu').1 (hpos hu').2.1).ne'
    exact Prod.ext ha (Prod.ext hb (mul_left_cancel₀ hne hmul))

/-- The lower count with multiplicity, using the smooth factorizations in Section 3. -/
def H1 : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℕ in atTop, ∃ A : Finset (ℕ × ℕ × ℕ),
    (∀ t ∈ A, t.1 ∈ Finset.Icc 1 x ∧ t.2.1 ∈ Finset.Icc 1 x ∧ t.2.2 ∈ Finset.Icc 1 x) ∧
    (∀ t ∈ A,
      let p := t.1 * t.2.1 * t.2.2 + 1
      p.Prime ∧ p ≤ x ∧ ∀ q : ℕ, q.Prime → q ∣ p - 1 →
        (q : ℝ) ≤ (x : ℝ) ^ ((2843115 : ℝ) / 10000000)) ∧
    C * (x : ℝ) ≤ (A.card : ℝ) * Real.log x

/-- The usual fourth moment of the divisor count, with the shifted index p - 1. -/
def H2 : Prop :=
  ∃ k : ℕ, ∃ D : ℝ, 0 < D ∧ ∀ᶠ x : ℕ in atTop,
    (∑ p ∈ Finset.range (x + 1), ((p - 1).divisors.card : ℝ) ^ 4) ≤
      D * (x : ℝ) * (Real.log x) ^ k

theorem main : H1 → H2 → OMA.R_Erdos821_erdos_821_variants_lichtman_R1.H1 := by
  rintro ⟨C, hC, hMany⟩ ⟨k, D, hD, hMoment⟩
  let δ : ℝ := 1 / 1000000
  have hδ : 0 < δ := by norm_num [δ]
  have hAbsorb := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
    ((isLittleO_log_rpow_rpow_atTop (↑(k + 2) : ℝ) hδ).def
      (show 0 < C ^ 2 / D by positivity))
  filter_upwards [hMany, hMoment, hAbsorb, eventually_ge_atTop (2 : ℕ)]
    with x hManyX hMomentX hAbsorbX hx2
  have hxR : (1 : ℝ) < x := by exact_mod_cast (show 1 < x by omega)
  have hpos : (0 : ℝ) < x := zero_lt_one.trans hxR
  have hLog : 0 ≤ Real.log (x : ℝ) := Real.log_nonneg hxR.le
  obtain ⟨A, hRange, hPrime, hManyA⟩ := hManyX
  let T := (Finset.Icc 1 x) ×ˢ ((Finset.Icc 1 x) ×ˢ (Finset.Icc 1 x))
  let f (t : ℕ × ℕ × ℕ) : ℕ := t.1 * t.2.1 * t.2.2 + 1
  let P := A.image f
  have hAT : A ⊆ T := by
    intro t ht
    obtain ⟨h1, h2, h3⟩ := hRange t ht
    exact Finset.mem_product.mpr ⟨h1, Finset.mem_product.mpr ⟨h2, h3⟩⟩
  have hMomentAll :
      (∑ p ∈ Finset.range (x + 1), ((T.filter (fun t => f t = p)).card : ℝ) ^ 2) ≤
      D * (x : ℝ) * (Real.log x) ^ k := by
    refine le_trans (Finset.sum_le_sum (fun p _ => ?_)) hMomentX
    have hle : ((T.filter (fun t => f t = p)).card : ℝ) ≤ ((p - 1).divisors.card : ℝ) ^ 2 := by
      exact_mod_cast triple_fiber_le_divisors_sq x p
    simpa only [← pow_mul] using pow_le_pow_left₀ (by positivity) hle 2
  have hCount : (A.card : ℝ) ^ 2 ≤ (P.card : ℝ) * (D * (x : ℝ) * (Real.log x) ^ k) := by
    have hi := card_image_moment f x hAT (fun t ht => (hPrime t ht).2.1)
    exact hi.trans (mul_le_mul_of_nonneg_left hMomentAll (by positivity))
  have hSquare :
      C ^ 2 * (x : ℝ) ^ 2 ≤ (P.card : ℝ) * (D * (Real.log x) ^ (k + 2)) * (x : ℝ) := by
    calc
      _ = (C * (x : ℝ)) ^ 2 := by ring
      _ ≤ ((A.card : ℝ) * Real.log x) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hManyA 2
      _ = (A.card : ℝ) ^ 2 * (Real.log x) ^ 2 := by ring
      _ ≤ ((P.card : ℝ) * (D * (x : ℝ) * (Real.log x) ^ k)) * (Real.log x) ^ 2 :=
        mul_le_mul_of_nonneg_right hCount (sq_nonneg _)
      _ = _ := by rw [pow_add]; ring
  have hScale : C ^ 2 * (x : ℝ) ≤ (P.card : ℝ) * (D * (Real.log x) ^ (k + 2)) := by
    by_contra! h
    have hbad := mul_lt_mul_of_pos_right h hpos
    nlinarith only [hSquare, hbad]
  have hLogPower : D * Real.log (x : ℝ) ^ (k + 2) ≤ C ^ 2 * (x : ℝ) ^ δ := by
    have h := hAbsorbX
    change ‖Real.log (x : ℝ) ^ (↑(k + 2) : ℝ)‖ ≤ (C ^ 2 / D) * ‖(x : ℝ) ^ δ‖ at h
    rw [Real.rpow_natCast, Real.norm_of_nonneg (pow_nonneg hLog _),
      Real.norm_of_nonneg (Real.rpow_nonneg hpos.le _)] at h
    calc
      _ ≤ D * (C ^ 2 / D * (x : ℝ) ^ δ) := mul_le_mul_of_nonneg_left h hD.le
      _ = _ := by field_simp [hD.ne']
  have hPow : (x : ℝ) ^ ((999999 : ℝ) / 1000000) * (x : ℝ) ^ δ = x := by
    rw [← Real.rpow_add hpos, show (999999 : ℝ) / 1000000 + δ = 1 by norm_num [δ], Real.rpow_one]
  have hPN : (x : ℝ) ^ ((999999 : ℝ) / 1000000) ≤ P.card := by
    by_contra! h
    have hbad := mul_lt_mul_of_pos_right h (show 0 < C ^ 2 * (x : ℝ) ^ δ by positivity)
    have hPr := mul_le_mul_of_nonneg_left hLogPower (show 0 ≤ (P.card : ℝ) by positivity)
    have hlimit : (P.card : ℝ) * (C ^ 2 * (x : ℝ) ^ δ) < C ^ 2 * (x : ℝ) := by
      refine hbad.trans_eq ?_
      calc
        _ = C ^ 2 * ((x : ℝ) ^ ((999999 : ℝ) / 1000000) * (x : ℝ) ^ δ) := by ring
        _ = _ := by rw [hPow]
    exact (not_lt_of_ge (hScale.trans hPr)) hlimit
  refine ⟨P, hPN, fun p hp => ?_⟩
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hp
  obtain ⟨hprime, hle, hsmooth⟩ := hPrime t ht
  refine ⟨hprime, hle, fun q hq hdiv => (hsmooth q hq hdiv).trans ?_⟩
  exact Real.rpow_le_rpow_of_exponent_le hxR.le (by norm_num)

end OMA.R_Erdos821_erdos_821_variants_lichtman_R1_H1_R1
