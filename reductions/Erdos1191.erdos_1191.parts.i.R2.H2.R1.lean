import OMAReductions.R_Erdos1191_erdos_1191_parts_i_R2

/-! A smallest Sidon witness to the negation survives both the large
early count and all the later lower count constraints. Erasing its
largest element breaks at least one constraint. A constraint affected
by that erasure counts the whole witness. A long enough horizon rules
out every early cutoff, and the growth from one scale to the next forces
the final count to be exactly one above its lower threshold. -/

open Set

namespace OMA.R_Erdos1191_erdos_1191_parts_i_R2_H2_R1

private theorem prefix_of_changed_erase {S : Finset ℕ} {a j : ℕ}
    (ha : a ∈ S) (hmax : ∀ x ∈ S, x ≤ a)
    (hchanged : (S.erase a).filter (· ≤ 2 ^ j) ≠ S.filter (· ≤ 2 ^ j)) :
    (∀ x ∈ S, x ≤ 2 ^ j) ∧ ((S.erase a).filter (· ≤ 2 ^ j)).card = S.card - 1 := by
  have hle : a ≤ 2 ^ j := by
    by_contra hn
    apply hchanged
    rw [Finset.filter_erase, Finset.erase_eq_of_notMem]
    exact fun h => hn (Finset.mem_filter.mp h).2
  have hall : ∀ x ∈ S, x ≤ 2 ^ j := fun x hx => (hmax x hx).trans hle
  refine ⟨hall, ?_⟩
  rw [Finset.filter_erase, Finset.filter_eq_self.mpr hall, Finset.card_erase_of_mem ha]

private theorem square_le_two_pow {n : ℕ} (h : 4 ≤ n) : n ^ 2 ≤ 2 ^ n := by
  induction n, h using Nat.le_induction with
  | base => decide
  | succ n hn ih =>
    have hn' := Nat.mul_le_mul_left n hn
    rw [pow_succ (2 : ℕ) n]
    calc
      (n + 1) ^ 2 ≤ 2 * n ^ 2 := by nlinarith
      _ ≤ 2 ^ n * 2 := by omega

private theorem next_scale_budget {c j : ℕ} (hc : 4 ≤ c) (hj : 8 ≤ j) :
    c ^ 2 * (j + 1) ≤ 2 * (c - 1) ^ 2 * j := by
  have hcomp := Nat.pow_le_pow_left (show 3 * c ≤ 4 * (c - 1) by omega) 2
  simp only [mul_pow] at hcomp
  have scaled : 9 * (c ^ 2 * (j + 1)) ≤ 9 * (2 * (c - 1) ^ 2 * j) := by
    calc
      _ = (3 ^ 2 * c ^ 2) * (j + 1) := by ring
      _ ≤ (4 ^ 2 * (c - 1) ^ 2) * (j + 1) := Nat.mul_le_mul_right _ hcomp
      _ = (c - 1) ^ 2 * (16 * (j + 1)) := by ring
      _ ≤ (c - 1) ^ 2 * (18 * j) := Nat.mul_le_mul_left _ (by omega)
      _ = _ := by ring
  exact Nat.le_of_mul_le_mul_left scaled (by decide)

/-- Exclude endpoint-saturated witnesses already above the spike threshold at the first scale. -/
def H1 : Prop :=
  ∀ d : ℕ, 0 < d → ∃ C₀ : ℕ, ∀ C ≥ C₀, ∀ J K : ℕ, J ≤ K →
    ∃ L ≥ K, ∀ M ≥ L, ∀ S : Finset ℕ,
      (S : Set ℕ) ⊆ Icc 1 (2 ^ M) → IsSidon (S : Set ℕ) →
      C * 2 ^ J < (S.filter (· ≤ 2 ^ J)).card ^ 2 * J →
      (∀ j ∈ Finset.Icc J M, 2 ^ j < d * (S.filter (· ≤ 2 ^ j)).card ^ 2 * j) →
      d * (S.card - 1) ^ 2 * M ≤ 2 ^ M → False

/-- Exclude endpoint-saturated witnesses whose first spike must occur after the first scale. -/
def H2 : Prop :=
  ∀ d : ℕ, 0 < d → ∃ C₀ : ℕ, ∀ C ≥ C₀, ∀ J K : ℕ, J ≤ K →
    ∃ L ≥ K, ∀ M ≥ L, ∀ S : Finset ℕ,
      (S : Set ℕ) ⊆ Icc 1 (2 ^ M) → IsSidon (S : Set ℕ) →
      (S.filter (· ≤ 2 ^ J)).card ^ 2 * J ≤ C * 2 ^ J →
      (∃ j ∈ Finset.Icc (J + 1) K, C * 2 ^ j < (S.filter (· ≤ 2 ^ j)).card ^ 2 * j) →
      (∀ j ∈ Finset.Icc J M, 2 ^ j < d * (S.filter (· ≤ 2 ^ j)).card ^ 2 * j) →
      d * (S.card - 1) ^ 2 * M ≤ 2 ^ M → False

theorem main : H1 → H2 → OMA.R_Erdos1191_erdos_1191_parts_i_R2.H2 := by
  intro h1 h2 d hd
  obtain ⟨C1, hC1⟩ := h1 d hd
  obtain ⟨C2, hC2⟩ := h2 d hd
  let C := max C1 C2
  refine ⟨C, ?_⟩
  intro J K hJK
  obtain ⟨L1, hL1, hA⟩ := hC1 C (le_max_left _ _) J K hJK
  obtain ⟨L2, _, hB⟩ := hC2 C (le_max_right _ _) J K hJK
  let Q := max K 8
  let M := max (max L1 L2) (d * (2 ^ Q) ^ 2 + 4)
  have hL1M : L1 ≤ M := (le_max_left L1 L2).trans (le_max_left _ _)
  have hL2M : L2 ≤ M := (le_max_right L1 L2).trans (le_max_left _ _)
  have hKM : K ≤ M := hL1.trans hL1M
  have hMq : d * (2 ^ Q) ^ 2 + 4 ≤ M := le_max_right _ _
  refine ⟨M, hKM, ?_⟩
  intro S hS hSid hLarge
  classical
  by_contra! hAll
  let large (T : Finset ℕ) : Prop :=
    ∃ j ∈ Finset.Icc J K, C * 2 ^ j < (T.filter (· ≤ 2 ^ j)).card ^ 2 * j
  let persists (T : Finset ℕ) : Prop :=
    ∀ j ∈ Finset.Icc J M, 2 ^ j < d * (T.filter (· ≤ 2 ^ j)).card ^ 2 * j
  let admissible := S.powerset.filter (fun T => large T ∧ persists T)
  have hnonempty : admissible.Nonempty :=
    ⟨S, Finset.mem_filter.mpr ⟨Finset.mem_powerset_self _, hLarge, hAll⟩⟩
  obtain ⟨T, hT, hMin⟩ := Finset.exists_min_image admissible Finset.card hnonempty
  obtain ⟨hTS, hTLarge, hTPersists⟩ := Finset.mem_filter.mp hT
  have hsub : T ⊆ S := Finset.mem_powerset.mp hTS
  have hcoe : (T : Set ℕ) ⊆ S := by exact_mod_cast hsub
  have hTBound : (T : Set ℕ) ⊆ Icc 1 (2 ^ M) := hcoe.trans hS
  have hSidT : IsSidon (T : Set ℕ) := hSid.subset hcoe
  have hAtM := hTPersists M (Finset.mem_Icc.mpr ⟨hJK.trans hKM, le_rfl⟩)
  rw [Finset.filter_eq_self.mpr (fun x hx => (hTBound (Finset.mem_coe.mpr hx)).2)] at hAtM
  have hM4 : 4 ≤ M := by omega
  have hCardLarge : 2 ^ Q < T.card := by
    by_contra! h
    have hD := Nat.mul_le_mul_left d (Nat.pow_le_pow_left h 2)
    have hDM : d * T.card ^ 2 ≤ M := hD.trans (by omega)
    have hprod := Nat.mul_le_mul_right M hDM
    exact (not_le_of_gt hAtM) (hprod.trans (by simpa only [pow_two] using square_le_two_pow hM4))
  have no_early_span (j : ℕ) (hj : j ≤ Q) (hspan : ∀ x ∈ T, x ≤ 2 ^ j) : False := by
    have hsubI : T ⊆ Finset.Icc 1 (2 ^ Q) := by
      intro x hx
      exact Finset.mem_Icc.mpr ⟨(hTBound (Finset.mem_coe.mpr hx)).1,
        (hspan x hx).trans (Nat.pow_le_pow_right (by decide) hj)⟩
    have hcard := Finset.card_le_card hsubI
    rw [Nat.card_Icc, Nat.add_sub_cancel] at hcard
    exact (not_le_of_gt hCardLarge) hcard
  have hTnonempty : T.Nonempty := by
    by_contra h
    have he : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    obtain ⟨j, _, hj⟩ := hTLarge
    simp [he] at hj
  let a := T.max' hTnonempty
  have ha : a ∈ T := T.max'_mem hTnonempty
  have hmax : ∀ x ∈ T, x ≤ a := fun x hx => T.le_max' x hx
  have hDrop : ¬ (large (T.erase a) ∧ persists (T.erase a)) := by
    intro h
    have hmem : T.erase a ∈ admissible :=
      Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr ((Finset.erase_subset _ _).trans hsub), h⟩
    exact (not_le_of_gt (Finset.card_erase_lt_of_mem ha)) (hMin _ hmem)
  by_cases hKeep : large (T.erase a)
  · have hfail : ∃ j ∈ Finset.Icc J M,
        d * ((T.erase a).filter (· ≤ 2 ^ j)).card ^ 2 * j ≤ 2 ^ j := by
      by_contra! hno
      exact hDrop ⟨hKeep, hno⟩
    obtain ⟨j, hj, hLow⟩ := hfail
    have hchange : (T.erase a).filter (· ≤ 2 ^ j) ≠ T.filter (· ≤ 2 ^ j) := by
      intro he
      rw [he] at hLow
      exact (not_le_of_gt (hTPersists j hj)) hLow
    obtain ⟨hSpan, hCard⟩ := prefix_of_changed_erase ha hmax hchange
    rw [hCard] at hLow
    have hQj : Q < j := lt_of_not_ge (fun he => no_early_span j he hSpan)
    have h8j : 8 ≤ j := (le_max_right K 8).trans hQj.le
    have h4 : 4 ≤ T.card := by
      have h2Q : 2 ≤ Q := (by decide : 2 ≤ 8).trans (le_max_right K 8)
      have h4pow : 4 ≤ (2 : ℕ) ^ Q := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) h2Q
      exact h4pow.trans hCardLarge.le
    have hjM : j = M := by
      by_contra h
      obtain ⟨hJj, hjM⟩ := Finset.mem_Icc.mp hj
      have hnext : j + 1 ≤ M := by omega
      have hAtNext := hTPersists (j + 1) (Finset.mem_Icc.mpr ⟨by omega, hnext⟩)
      have hspan' : ∀ x ∈ T, x ≤ 2 ^ (j + 1) := fun x hx =>
        (hSpan x hx).trans (Nat.pow_le_pow_right (by decide) (Nat.le_succ j))
      rw [Finset.filter_eq_self.mpr hspan'] at hAtNext
      apply (not_le_of_gt hAtNext)
      calc
        _ = d * (T.card ^ 2 * (j + 1)) := by ring
        _ ≤ d * (2 * (T.card - 1) ^ 2 * j) := Nat.mul_le_mul_left d (next_scale_budget h4 h8j)
        _ = 2 * (d * (T.card - 1) ^ 2 * j) := by ring
        _ ≤ 2 * 2 ^ j := Nat.mul_le_mul_left 2 hLow
        _ = 2 ^ (j + 1) := by rw [pow_succ]; ring
    rw [hjM] at hLow
    by_cases hInitial : C * 2 ^ J < (T.filter (· ≤ 2 ^ J)).card ^ 2 * J
    · exact hA M hL1M T hTBound hSidT hInitial hTPersists hLow
    · obtain ⟨k, hk, hHigh⟩ := hTLarge
      obtain ⟨hJk, hkK⟩ := Finset.mem_Icc.mp hk
      have hkne : k ≠ J := fun he => hInitial (he ▸ hHigh)
      have hk' : k ∈ Finset.Icc (J + 1) K := Finset.mem_Icc.mpr ⟨by omega, hkK⟩
      exact hB M hL2M T hTBound hSidT (le_of_not_gt hInitial) ⟨k, hk', hHigh⟩ hTPersists hLow
  · obtain ⟨j, hj, hHigh⟩ := hTLarge
    have hLow : ((T.erase a).filter (· ≤ 2 ^ j)).card ^ 2 * j ≤ C * 2 ^ j :=
      le_of_not_gt (fun h => hKeep ⟨j, hj, h⟩)
    have hchange : (T.erase a).filter (· ≤ 2 ^ j) ≠ T.filter (· ≤ 2 ^ j) := by
      intro he
      rw [he] at hLow
      exact (not_le_of_gt hHigh) hLow
    obtain ⟨hSpan, _⟩ := prefix_of_changed_erase ha hmax hchange
    exact no_early_span j ((Finset.mem_Icc.mp hj).2.trans (le_max_left K 8)) hSpan

end OMA.R_Erdos1191_erdos_1191_parts_i_R2_H2_R1
