import OMAReductions.R_DiophantineTuple_noIntegralDiophantineFiveTuple_R1

/-! Jones's gap lemma, as used in Lemma 1 of He, Togbé and Ziegler,
splits the three smallest entries into Euler triples and triples with
a large gap. The signed companion is nonnegative because multiplying
it by the middle entry and adding one gives a square. Factoring the
product of the two companions then proves the gap. -/

open DiophantineTuple

namespace OMA.R_DiophantineTuple_noIntegralDiophantineFiveTuple_R1_H2_R1

private theorem jones_gap_int {a b c r s t : ℤ}
    (ha : 0 < a) (hab : a < b) (hbc : b < c)
    (hr0 : 0 ≤ r) (hs0 : 0 ≤ s) (ht0 : 0 ≤ t)
    (hr : r ^ 2 = a * b + 1) (hs : s ^ 2 = a * c + 1) (ht : t ^ 2 = b * c + 1) :
    let m := a + b + c + 2 * a * b * c - 2 * r * s * t
    c = a + b + 2 * r ∨ (1 ≤ m ∧ 4 * a * b * m < c) := by
  intro m
  let p := a + b + c + 2 * a * b * c + 2 * r * s * t
  have hb : 0 < b := ha.trans hab
  have hc : 0 < c := hb.trans hbc
  have hp : 0 < p := by dsimp [p]; positivity
  have hCompSquare : b * m + 1 = (r * t - b * s) ^ 2 := by
    calc
      _ = (a * b + 1) * (b * c + 1) + b ^ 2 * (a * c + 1) -
          2 * b * r * s * t := by dsimp [m]; ring
      _ = _ := by rw [← hr, ← hs, ← ht]; ring
  have hm0 : 0 ≤ m := by
    by_contra! hneg
    have hmNeg : m ≤ -1 := by omega
    have hmul := mul_le_mul_of_nonneg_left hmNeg hb.le
    have hb2 : 2 ≤ b := by omega
    linarith [sq_nonneg (r * t - b * s)]
  have hDelta : m * p = (c - a - b) ^ 2 - 4 * r ^ 2 := by
    calc
      _ = (a + b + c + 2 * a * b * c) ^ 2 - 4 * (r ^ 2 * s ^ 2 * t ^ 2) := by
        dsimp [m, p]
        ring
      _ = _ := by rw [hr, hs, ht]; ring
  have hFact : (c - a - b - 2 * r) * (c - a - b + 2 * r) = m * p := by
    rw [hDelta]
    ring
  have har : a ≤ r := by
    apply (sq_le_sq₀ ha.le hr0).mp
    rw [hr]
    have h := mul_le_mul_of_nonneg_left hab.le ha.le
    nlinarith
  have hplus : 0 < c - a - b + 2 * r := by linarith
  by_cases hm : m = 0
  · rw [hm, zero_mul] at hFact
    have hz := (mul_eq_zero.mp hFact).resolve_right hplus.ne'
    exact Or.inl (by linarith)
  · have hm1 : 1 ≤ m := by omega
    have hminus : 0 ≤ c - a - b - 2 * r := by
      by_contra! h
      have hneg := mul_neg_of_neg_of_pos h hplus
      rw [hFact] at hneg
      exact (not_lt_of_ge (mul_nonneg hm0 hp.le)) hneg
    have hroots : a * b * c ≤ r * s * t := by
      apply (sq_le_sq₀ (by positivity) (by positivity)).mp
      calc
        _ = (a * b) * (a * c) * (b * c) := by ring
        _ ≤ (a * b + 1) * (a * c + 1) * (b * c + 1) := by
          gcongr <;> first | positivity | linarith
        _ = _ := by rw [← hr, ← hs, ← ht]; ring
    have hpLarge : 4 * a * b * c < p := by
      dsimp [p]
      linarith
    have hDUpper : m * p ≤ c ^ 2 := by
      rw [hDelta]
      have hbase : 0 ≤ c - a - b := by linarith
      have hsquares : (c - a - b) ^ 2 ≤ c ^ 2 :=
        (sq_le_sq₀ hbase hc.le).mpr (by linarith)
      linarith [sq_nonneg r]
    have hLarge : (4 * a * b * m) * c < c * c := by
      calc
        _ = m * (4 * a * b * c) := by ring
        _ < m * p := mul_lt_mul_of_pos_left hpLarge (by omega)
        _ ≤ _ := by simpa only [pow_two] using hDUpper
    refine Or.inr ⟨hm1, ?_⟩
    by_contra! h
    exact (not_le_of_gt hLarge) (mul_le_mul_of_nonneg_right h hc.le)

/-- The three smallest entries of a putative quintuple satisfy Jones's gap. -/
theorem euler_or_large_gap {a b c d e : ℕ} (ha : 0 < a) (hab : a < b) (hbc : b < c)
    (h : IsIntegralDiophantineTuple {a, b, c, d, e}) :
    (∃ r : ℕ, r ^ 2 = a * b + 1 ∧ c = a + b + 2 * r) ∨ 4 * a * b < c := by
  obtain ⟨r, hr⟩ := h.2 a (by simp) b (by simp) (ne_of_lt hab)
  obtain ⟨s, hs⟩ := h.2 a (by simp) c (by simp) (ne_of_lt (hab.trans hbc))
  obtain ⟨t, ht⟩ := h.2 b (by simp) c (by simp) (ne_of_lt hbc)
  have hrN : r ^ 2 = a * b + 1 := by simpa only [pow_two] using hr.symm
  have hgap := jones_gap_int (a := a) (b := b) (c := c) (r := r) (s := s) (t := t)
    (by exact_mod_cast ha) (by exact_mod_cast hab) (by exact_mod_cast hbc)
    (by positivity) (by positivity) (by positivity)
    (by exact_mod_cast hrN)
    (by exact_mod_cast (show s ^ 2 = a * c + 1 by simpa only [pow_two] using hs.symm))
    (by exact_mod_cast (show t ^ 2 = b * c + 1 by simpa only [pow_two] using ht.symm))
  dsimp only at hgap
  rcases hgap with hEuler | ⟨hm, hBig⟩
  · exact Or.inl ⟨r, hrN, by exact_mod_cast hEuler⟩
  · have hbase : (0 : ℤ) ≤ 4 * (a : ℤ) * (b : ℤ) := by positivity
    have hstep := mul_le_mul_of_nonneg_left hm hbase
    rw [mul_one] at hstep
    exact Or.inr (by exact_mod_cast hstep.trans_lt hBig)

/-- Irregular extensions of triples of Euler type, the case of Section 8. -/
def H1 : Prop :=
  ∀ a b c d e : ℕ, 0 < a → a < b → b < c → c < d → d < e →
    d ≠ regularExtension a b c →
    (∃ r : ℕ, r ^ 2 = a * b + 1 ∧ c = a + b + 2 * r) →
    ¬ IsIntegralDiophantineTuple {a, b, c, d, e}

/-- Irregular extensions in the large-gap regime of Section 9. -/
def H2 : Prop :=
  ∀ a b c d e : ℕ, 0 < a → a < b → b < c → c < d → d < e →
    d ≠ regularExtension a b c → 4 * a * b < c →
    ¬ IsIntegralDiophantineTuple {a, b, c, d, e}

theorem main : H1 → H2 → OMA.R_DiophantineTuple_noIntegralDiophantineFiveTuple_R1.H2 := by
  intro h1 h2 a b c d e ha hab hbc hcd hde hd tuple
  rcases euler_or_large_gap ha hab hbc tuple with hEuler | hGap
  · exact h1 a b c d e ha hab hbc hcd hde hd hEuler tuple
  · exact h2 a b c d e ha hab hbc hcd hde hd hGap tuple

end OMA.R_DiophantineTuple_noIntegralDiophantineFiveTuple_R1_H2_R1
