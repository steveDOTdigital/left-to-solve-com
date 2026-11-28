import FormalConjectures.OptimizationConstants.«7b»
import Mathlib.RingTheory.AlgebraicIndependent.Defs
import Mathlib.NumberTheory.Divisors

/-! Use the normalized weight-four Eisenstein series at i. The
independence of this value and pi follows from the square-lattice
period theorem. Its evaluation follows from the two period formulas
in Nesterenko's discussion of Corollaries 3 through 5. If Gamma(1/4)
were rational, those formulas would give a nonzero rational polynomial
relation between the two independent numbers. -/

open MvPolynomial
open scoped BigOperators

namespace OMA.R_Constant7b_irrational_gamma_one_div_four_R1

private theorem irrational_pow_mul_of_independent {x y : ℝ}
    (h : AlgebraicIndependent ℚ (fun b : Bool => if b then y else x)) (n : ℕ) :
    Irrational (x ^ n * y) := by
  unfold Irrational
  rintro ⟨q, hq⟩
  let p : MvPolynomial Bool ℚ := X false ^ n * X true - C q
  have hz : aeval (fun b : Bool => if b then y else x) p = 0 := by
    simp only [p, map_sub, map_mul, map_pow, aeval_X, aeval_C]
    change x ^ n * y - (q : ℝ) = 0
    exact sub_eq_zero.mpr hq.symm
  have hp := h.eq_zero_of_aeval_eq_zero p hz
  have evalZero := congrArg (eval (fun _ : Bool => (0 : ℚ))) hp
  have evalOne := congrArg (eval (fun _ : Bool => (1 : ℚ))) hp
  have h0 : 0 - q = 0 := by
    simpa only [p, map_sub, map_mul, map_pow, eval_X, eval_C, mul_zero, map_zero] using evalZero
  have h1 : 1 - q = 0 := by
    simpa only [p, map_sub, map_mul, map_pow, eval_X, eval_C, one_pow, mul_one, map_zero] using evalOne
  linarith

private theorem weight_four_normalization {E w g : ℝ}
    (hE : E = 3 * (w / Real.pi) ^ 4) (hw : w * Real.sqrt (8 * Real.pi) = g ^ 2) :
    Real.pi ^ 6 * E = (3 / 64) * g ^ 8 := by
  have hs := Real.sq_sqrt (show 0 ≤ 8 * Real.pi by positivity)
  have hs4 : Real.sqrt (8 * Real.pi) ^ 4 = (8 * Real.pi) ^ 2 := by
    calc
      _ = (Real.sqrt (8 * Real.pi) ^ 2) ^ 2 := by ring
      _ = _ := congrArg (fun t : ℝ => t ^ 2) hs
  have h4 := congrArg (fun t : ℝ => t ^ 4) hw
  change (w * Real.sqrt (8 * Real.pi)) ^ 4 = (g ^ 2) ^ 4 at h4
  rw [mul_pow, hs4] at h4
  rw [hE]
  calc
    _ = (3 / 64) * (w ^ 4 * (8 * Real.pi) ^ 2) := by
      field_simp [Real.pi_ne_zero]
      ring
    _ = (3 / 64) * (g ^ 2) ^ 4 := by rw [h4]
    _ = _ := by ring

/-- Algebraic independence of pi and the normalized weight-four Eisenstein value at i. -/
def H1 : Prop :=
  AlgebraicIndependent ℚ (fun b : Bool => if b then
    1 + 240 * ∑' n : ℕ, (∑ d ∈ (n + 1).divisors, (d : ℝ) ^ 3) *
      Real.exp (-2 * Real.pi * (n + 1 : ℕ))
    else Real.pi)

/-- The weight-four value and Gamma value expressed in terms of the same real period. -/
def H2 : Prop :=
  ∃ w : ℝ,
    1 + 240 * (∑' n : ℕ, (∑ d ∈ (n + 1).divisors, (d : ℝ) ^ 3) *
      Real.exp (-2 * Real.pi * (n + 1 : ℕ))) = 3 * (w / Real.pi) ^ 4 ∧
    w * Real.sqrt (8 * Real.pi) = Real.Gamma (1 / 4) ^ 2

theorem main : H1 → H2 → type_of% @Constant7b.irrational_gamma_one_div_four := by
  rintro hInd ⟨w, hE, hw⟩
  have hIrr := irrational_pow_mul_of_independent hInd 6
  have hPower := weight_four_normalization hE hw
  unfold Irrational
  rintro ⟨q, hq⟩
  apply hIrr
  refine ⟨(3 : ℚ) / 64 * q ^ 8, ?_⟩
  push_cast
  rw [hq]
  simpa only [Nat.cast_add, Nat.cast_one] using hPower.symm

end OMA.R_Constant7b_irrational_gamma_one_div_four_R1
