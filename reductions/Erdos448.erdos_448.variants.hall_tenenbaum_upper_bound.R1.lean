import FormalConjectures.ErdosProblems.«448»

/-! Hall and Tenenbaum's limiting distribution determines the densities at
its continuity points. An upper bound on the lower densities transfers to
the strict-threshold upper density by choosing a continuity point between
the requested threshold and twice that threshold. The distribution and
its small-threshold estimate are stated separately. -/

open Filter Asymptotics Set
open scoped Topology
open Erdos448

namespace OMA.R_Erdos448_erdos_448_variants_hall_tenenbaum_upper_bound_R1

private theorem partial_mono {A B : Set ℕ} (h : A ⊆ B) (x : ℕ) :
    A.partialDensity univ x ≤ B.partialDensity univ x := by
  unfold Set.partialDensity
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast Set.ncard_le_ncard
    (show (A ∩ univ) ∩ Iio x ⊆ (B ∩ univ) ∩ Iio x from
      fun _ ⟨⟨ha, hu⟩, hx⟩ => ⟨⟨h ha, hu⟩, hx⟩)

private theorem upper_mono {A B : Set ℕ} (h : A ⊆ B) :
    A.upperDensity ≤ B.upperDensity := by
  unfold Set.upperDensity
  exact limsup_le_limsup (Eventually.of_forall (partial_mono h))
    (isCoboundedUnder_le_of_le atTop (x := 0) (fun x => by positivity))
    (isBoundedUnder_of ⟨1, B.partialDensity_le_one univ⟩)

private theorem upper_nonneg (A : Set ℕ) : 0 ≤ A.upperDensity := by
  unfold Set.upperDensity
  apply le_limsup_of_le (isBoundedUnder_of ⟨1, A.partialDensity_le_one univ⟩)
  intro c hc
  obtain ⟨n, hn⟩ := hc.exists
  exact (by positivity : 0 ≤ A.partialDensity univ n).trans hn

private theorem strict_event_subset {e z : ℝ} (he : 0 < e) (hz : e < z) :
    {n : ℕ | (tauPlus n : ℝ) < e * (n.divisors.card : ℝ)} ⊆
      {n : ℕ | (tauPlus n : ℝ) / (n.divisors.card : ℝ) ≤ z} := by
  intro n hn
  change (tauPlus n : ℝ) < e * (n.divisors.card : ℝ) at hn
  have hcard : 0 < (n.divisors.card : ℝ) := by
    by_contra! h
    exact (not_lt_of_ge ((mul_nonpos_of_nonneg_of_nonpos he.le h).trans
      (Nat.cast_nonneg (tauPlus n)))) hn
  exact ((div_lt_iff₀ hcard).mpr hn).le.trans hz.le

/-- The limiting distribution, restricted to the range needed for the upper bound. -/
def H1 : Prop :=
  ∃ F : ℝ → ℝ, Monotone F ∧ ∀ z : ℝ, 0 < z → z < 1 → ContinuousAt F z →
    {n : ℕ | (tauPlus n : ℝ) / (n.divisors.card : ℝ) ≤ z}.HasDensity (F z)

/-- The quantitative estimate for the lower density of the weak-threshold event. -/
def H2 : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ z : ℝ, 0 < z → z < 1 →
    {n : ℕ | (tauPlus n : ℝ) / (n.divisors.card : ℝ) ≤ z}.lowerDensity ≤
      C * (z * Real.log (2 / z))

theorem main : H1 → H2 → type_of% @Erdos448.erdos_448.variants.hall_tenenbaum_upper_bound := by
  rintro ⟨F, hmono, hF⟩ ⟨C, hC, hbound⟩
  have hdense := Set.Countable.dense_compl ℝ hmono.countable_not_continuousAt
  apply IsBigO.of_bound (2 * C)
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num))]
    with e he heHalf
  change 0 < e at he
  change e < 1 / 2 at heHalf
  obtain ⟨z, hz, hcont⟩ := hdense.inter_open_nonempty (Ioo e (2 * e)) isOpen_Ioo
    (nonempty_Ioo.mpr (by linarith))
  have hc : ContinuousAt F z := by simpa using hcont
  have hz0 : 0 < z := he.trans hz.1
  have hz1 : z < 1 := hz.2.trans (by linarith)
  have hden := hF z hz0 hz1 hc
  have hu : {n : ℕ | (tauPlus n : ℝ) / (n.divisors.card : ℝ) ≤ z}.upperDensity = F z :=
    Filter.Tendsto.limsup_eq hden
  have hl : {n : ℕ | (tauPlus n : ℝ) / (n.divisors.card : ℝ) ≤ z}.lowerDensity = F z :=
    Filter.Tendsto.liminf_eq hden
  have htransfer := upper_mono (strict_event_subset he hz.1)
  rw [hu] at htransfer
  have hlower := hbound z hz0 hz1
  rw [hl] at hlower
  have hlog : 0 ≤ Real.log (2 / e) :=
    Real.log_nonneg ((le_div_iff₀ he).mpr (by linarith))
  have hlogMono : Real.log (2 / z) ≤ Real.log (2 / e) :=
    Real.log_le_log (by positivity) (div_le_div_of_nonneg_left (by norm_num) he hz.1.le)
  have hscale : z * Real.log (2 / z) ≤ 2 * e * Real.log (2 / e) :=
    (mul_le_mul_of_nonneg_left hlogMono hz0.le).trans
      (mul_le_mul_of_nonneg_right hz.2.le hlog)
  simp only [Real.norm_eq_abs, abs_of_nonneg (upper_nonneg _),
    abs_of_nonneg (mul_nonneg he.le hlog)]
  calc
    _ ≤ C * (z * Real.log (2 / z)) := htransfer.trans hlower
    _ ≤ C * (2 * e * Real.log (2 / e)) := mul_le_mul_of_nonneg_left hscale hC.le
    _ = _ := by ring

end OMA.R_Erdos448_erdos_448_variants_hall_tenenbaum_upper_bound_R1
