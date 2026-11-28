import OMAReductions.R_oeis_a387947_R1

/-! In the prime-square branch, the candidates are the odd numbers
`2 * p * t + 1` with `1 ≤ t ≤ (p - 1) / 2`. Every composite
candidate has a prime factor smaller than `p`, so a finite sieve gives
an exact count. -/

namespace OMA.R_oeis_a387947_R1_H1_R1

private theorem candidate_bounds {p t : ℕ} (hp : 7 ≤ p) (ht : 1 ≤ t)
    (htop : t ≤ (p - 1) / 2) : p < 2 * p * t + 1 ∧ 2 * p * t + 1 < p ^ 2 := by
  have hlo := Nat.mul_le_mul_left p (show 1 ≤ 2 * t by omega)
  rw [Nat.mul_one] at hlo
  have hhi := Nat.mul_le_mul_left p (show 2 * t ≤ p - 1 by omega)
  rw [Nat.mul_sub, Nat.mul_one] at hhi
  have hs : p ≤ p * p := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left p (show 1 ≤ p by omega)
  rw [show 2 * p * t = p * (2 * t) by ring, pow_two]
  omega

/-- The sieve keeps exactly the prime candidates in the index interval. -/
theorem mem_survivors_iff {p t : ℕ} (hp : 7 ≤ p) :
    t ∈ ((Finset.Icc 1 ((p - 1) / 2)).filter (fun t =>
      ∀ d : Fin p, ¬ (d.val.Prime ∧ d.val ∣ 2 * p * t + 1))) ↔
      1 ≤ t ∧ t ≤ (p - 1) / 2 ∧ (2 * p * t + 1).Prime := by
  simp only [Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨ht, htop⟩, hs⟩
    have hb := candidate_bounds hp ht htop
    refine ⟨ht, htop, ?_⟩
    by_contra hn
    have hmin := Nat.minFac_sq_le_self (by omega : 0 < 2 * p * t + 1) hn
    have hlt : (2 * p * t + 1).minFac < p := by
      by_contra! h
      exact (not_le_of_gt hb.2) ((Nat.pow_le_pow_left h 2).trans hmin)
    exact hs ⟨_, hlt⟩ ⟨Nat.minFac_prime (by omega), Nat.minFac_dvd _⟩
  · rintro ⟨ht, htop, hq⟩
    refine ⟨⟨ht, htop⟩, fun d hd => ?_⟩
    have he := (Nat.prime_dvd_prime_iff_eq hd.1 hq).mp hd.2
    have hlt := d.isLt
    have hb := (candidate_bounds hp ht htop).1
    omega

/-- An odd sieve prime below p can exclude indices in only one residue class. -/
theorem excluded_indices_modEq {p d t u : ℕ} (hp : p.Prime) (hd : d.Prime)
    (hd2 : 2 < d) (hdp : d < p) (ht : d ∣ (2 * p * t + 1)) (hu : d ∣ (2 * p * u + 1)) :
    t ≡ u [MOD d] := by
  have hn : ¬ d ∣ 2 * p := by
    intro h
    rcases hd.dvd_mul.mp h with h | h
    · have := Nat.le_of_dvd (by decide : 0 < 2) h
      omega
    · exact (ne_of_lt hdp) ((Nat.prime_dvd_prime_iff_eq hd hp).mp h)
  have hcong := (Nat.modEq_zero_iff_dvd.mpr ht).trans (Nat.modEq_zero_iff_dvd.mpr hu).symm
  exact Nat.ModEq.cancel_left_of_coprime
    ((hd.coprime_iff_not_dvd.mpr hn).gcd_eq_one) (hcong.add_right_cancel' 1)

private theorem candidate_mod (p t : ℕ) : (2 * p * t + 1) ≡ 1 [MOD p] := by
  apply Nat.ModEq.symm
  have hle : 1 ≤ 2 * p * t + 1 := by omega
  apply (Nat.modEq_iff_dvd' hle).mpr
  refine ⟨2 * t, ?_⟩
  rw [Nat.add_sub_cancel]
  ring

private theorem index_of_prime {p r : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p)
    (hr : r.Prime) (hb : r ≤ p ^ 2) (hc : r ≡ 1 [MOD p]) :
    ∃ t ∈ ((Finset.Icc 1 ((p - 1) / 2)).filter (fun t =>
      ∀ d : Fin p, ¬ (d.val.Prime ∧ d.val ∣ 2 * p * t + 1))), (2 * p * t + 1) = r := by
  have hr2 := hr.two_le
  obtain ⟨k, hk⟩ := (Nat.modEq_iff_dvd' (show 1 ≤ r by omega)).mp hc.symm
  have hrep : r = p * k + 1 := by omega
  have hk0 : k ≠ 0 := by
    intro h
    simp [h] at hrep
    omega
  have hkp : k < p := by
    by_contra! h
    have hm := Nat.mul_le_mul_left p h
    rw [pow_two] at hb
    omega
  have hrne : r ≠ 2 := by
    intro h
    rw [h] at hc
    change 2 % p = 1 % p at hc
    rw [Nat.mod_eq_of_lt (show 2 < p by omega),
      Nat.mod_eq_of_lt (show 1 < p by omega)] at hc
    omega
  obtain ⟨b, hbOdd⟩ := hr.odd_of_ne_two hrne
  obtain ⟨a, haOdd⟩ := hp.odd_of_ne_two (by omega)
  have hprod : 2 ∣ p * k := ⟨b, by omega⟩
  have hn : ¬ 2 ∣ p := by omega
  obtain ⟨t, ht⟩ := (Nat.prime_two.dvd_mul.mp hprod).resolve_left hn
  have he : 2 * p * t + 1 = r := by
    rw [hrep, ht]
    ring
  refine ⟨t, (mem_survivors_iff hp7).mpr ⟨by omega, by omega, he.symm ▸ hr⟩, he⟩

/-- Two distinct survivors are equivalent to the two ordered prime witnesses. -/
theorem sieve_iff {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p) :
    let survivors := ((Finset.Icc 1 ((p - 1) / 2)).filter (fun t =>
      ∀ d : Fin p, ¬ (d.val.Prime ∧ d.val ∣ 2 * p * t + 1)))
    2 ≤ survivors.card ↔ ∃ r s : ℕ, r.Prime ∧ s.Prime ∧ s < r ∧ r ≤ p ^ 2 ∧
      (r ≡ 1 [MOD p]) ∧ (s ≡ 1 [MOD p]) := by
  intro survivors
  rw [show 2 ≤ survivors.card ↔ 1 < survivors.card by omega,
    Finset.one_lt_card_iff]
  constructor
  · rintro ⟨a, b, ha, hb, hn⟩
    have ordered (t u : ℕ) (ht : t ∈ survivors) (hu : u ∈ survivors) (hlt : t < u) :
        ∃ r s : ℕ, r.Prime ∧ s.Prime ∧ s < r ∧ r ≤ p ^ 2 ∧
          (r ≡ 1 [MOD p]) ∧ (s ≡ 1 [MOD p]) := by
      obtain ⟨_, _, htP⟩ := (mem_survivors_iff hp7).mp ht
      obtain ⟨hu1, hu2, huP⟩ := (mem_survivors_iff hp7).mp hu
      have hpos : 0 < 2 * p := by positivity
      have hlt' := Nat.mul_lt_mul_of_pos_left hlt hpos
      exact ⟨2 * p * u + 1, 2 * p * t + 1, huP, htP,
        by simpa only [add_lt_add_iff_right] using hlt',
        (candidate_bounds hp7 hu1 hu2).2.le, candidate_mod p u, candidate_mod p t⟩
    rcases lt_or_gt_of_ne hn with h | h
    · exact ordered a b ha hb h
    · exact ordered b a hb ha h
  · rintro ⟨r, s, hr, hs, hsr, hrp, hrm, hsm⟩
    obtain ⟨a, ha, har⟩ := index_of_prime hp hp7 hr hrp hrm
    obtain ⟨b, hb, hbs⟩ := index_of_prime hp hp7 hs (hsr.le.trans hrp) hsm
    exact ⟨a, b, ha, hb, fun he => (ne_of_gt hsr)
      (har.symm.trans ((congrArg (fun t => 2 * p * t + 1) he).trans hbs))⟩

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
private theorem small_sieve : ∀ p : Fin 101, p.val.Prime → 7 ≤ p.val →
    2 ≤ ((Finset.Icc 1 ((p.val - 1) / 2)).filter (fun t =>
      ∀ d : Fin p.val, ¬ (d.val.Prime ∧ d.val ∣ 2 * p.val * t + 1))).card := by
  decide +kernel

/-- When p is one or two modulo three, the same residue of the index is removed. -/
private theorem three_filter_subset {p a : ℕ} (ha : a = 1 ∨ a = 2)
    (hp : p % 3 = a) :
    ((Finset.Icc 1 ((p - 1) / 2)).filter (fun t =>
      t % 3 ≠ a ∧ ∀ d : Fin p, 3 < d.val → ¬ (d.val.Prime ∧ d.val ∣ 2 * p * t + 1))) ⊆
    ((Finset.Icc 1 ((p - 1) / 2)).filter (fun t =>
      ∀ d : Fin p, ¬ (d.val.Prime ∧ d.val ∣ 2 * p * t + 1))) := by
  intro t ht
  obtain ⟨hIcc, hThree, hBig⟩ := Finset.mem_filter.mp ht
  refine Finset.mem_filter.mpr ⟨hIcc, fun d hd => ?_⟩
  by_cases hBigD : 3 < d.val
  · exact hBig d hBigD hd
  have hd2 := hd.1.two_le
  have hcases : d.val = 2 ∨ d.val = 3 := by omega
  rcases hcases with h | h
  · have hm := Nat.dvd_iff_mod_eq_zero.mp hd.2
    rw [h] at hm
    change (2 * p * t + 1) % 2 = 0 at hm
    rw [show 2 * p * t = 2 * (p * t) by ring] at hm
    omega
  · have hm := Nat.dvd_iff_mod_eq_zero.mp hd.2
    rw [h] at hm
    change (2 * p * t + 1) % 3 = 0 at hm
    rw [Nat.add_mod (2 * p * t) 1 3, Nat.mul_mod (2 * p) t 3,
      Nat.mul_mod 2 p 3, hp] at hm
    have ht3 : t % 3 = 0 ∨ t % 3 = 1 ∨ t % 3 = 2 := by omega
    rcases ha with rfl | rfl
    · rcases ht3 with ht0 | ht1 | ht2
      · norm_num [ht0] at hm
      · exact hThree ht1
      · norm_num [ht2] at hm
    · rcases ht3 with ht0 | ht1 | ht2
      · norm_num [ht0] at hm
      · norm_num [ht1] at hm
      · exact hThree ht2

/-- In the first residue class, indices congruent to one modulo three are excluded. -/
def H1 : Prop := ∀ p : ℕ, p.Prime → 101 ≤ p → p % 3 = 1 →
  2 ≤ ((Finset.Icc 1 ((p - 1) / 2)).filter (fun t =>
    t % 3 ≠ 1 ∧ ∀ d : Fin p, 3 < d.val → ¬ (d.val.Prime ∧ d.val ∣ 2 * p * t + 1))).card

/-- In the second residue class, indices congruent to two modulo three are excluded. -/
def H2 : Prop := ∀ p : ℕ, p.Prime → 101 ≤ p → p % 3 = 2 →
  2 ≤ ((Finset.Icc 1 ((p - 1) / 2)).filter (fun t =>
    t % 3 ≠ 2 ∧ ∀ d : Fin p, 3 < d.val → ¬ (d.val.Prime ∧ d.val ∣ 2 * p * t + 1))).card

theorem main : H1 → H2 → OMA.R_oeis_a387947_R1.H1 := by
  intro h1 h2 p hp hp7
  apply (sieve_iff hp hp7).mp
  by_cases hp101 : p < 101
  · exact small_sieve ⟨p, hp101⟩ hp hp7
  have hnot : ¬ 3 ∣ p := fun h => by
    have he := (Nat.prime_dvd_prime_iff_eq (by decide : Nat.Prime 3) hp).mp h
    omega
  have hp3 : p % 3 = 1 ∨ p % 3 = 2 := by
    have hn : p % 3 ≠ 0 := fun h => hnot (Nat.dvd_iff_mod_eq_zero.mpr h)
    omega
  rcases hp3 with h | h
  · exact (h1 p hp (by omega) h).trans (Finset.card_le_card (three_filter_subset (Or.inl rfl) h))
  · exact (h2 p hp (by omega) h).trans (Finset.card_le_card (three_filter_subset (Or.inr rfl) h))

end OMA.R_oeis_a387947_R1_H1_R1
