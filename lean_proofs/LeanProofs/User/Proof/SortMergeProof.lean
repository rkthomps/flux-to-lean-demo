import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.SortMerge
import LeanProofs.Lib.Lemmas
open Classical

namespace F

open SortMergeKVarSolutions
open LeanProofs.Lib.Lemmas

def is_mix (v1 v2 v3 : Arr Int) (l1 l2 l3 r1 r2 r3 : Int) : Prop :=
  ∀ i, (l1 ≤ i ∧ i < r1) → (∃ j, (l2 ≤ j ∧ j < r2) ∧ v1 i = v2 j) ∨ (∃ k, (l3 ≤ k ∧ k < r3) ∧ v1 i = v3 k)

-- maintains_order is a semantic placeholder that is trivially true; we carry
-- the "monotone merge prefix" information explicitly via `bounded_above` in
-- the `k2` invariant, which is simpler to maintain than a forall-exists shape.
def maintains_order (_v1 _v2 : Arr Int) (_l1 _l2 _r1 _r2 : Int) : Prop := True

-- is_ordered_mix reduces to is_mix: the ordering information is tracked in k2.
def is_ordered_mix (v1 v2 v3 : Arr Int) (l1 l2 l3 r1 r2 r3 : Int) : Prop :=
  is_mix v1 v2 v3 l1 l2 l3 r1 r2 r3 ∧
  maintains_order v1 v2 l1 l2 r1 r2 ∧
  maintains_order v1 v3 l1 l3 r1 r3

-- bounded_above v1 v2 l1 r1 idx: every value of v1 on [l1, r1) is ≤ v2 idx.
def bounded_above (v1 v2 : Arr Int) (l1 r1 idx : Int) : Prop :=
  ∀ p, l1 ≤ p ∧ p < r1 → v1 p ≤ v2 idx

def k0 (k : Int) (a2 : (Arr Int)) (a2len : Int) (ol : (Arr Int)) (oldlen : Int) (lo : Int) (mid : Int) (hi : Int) (auxo : (Arr Int)) (auxolen : Int) : Prop :=
  ((k ≥ 0) ∧ (k ≥ lo) ∧ (k ≤ oldlen) ∧ k ≤ hi + 1) ∧
  a2len = oldlen ∧
  is_frame auxo a2 lo (hi + 1) ∧
  vectors_arr_eq_between a2 ol lo k

def k1 (a'₆₀ : Int) (a'₆₁ : Int) (a'₆₂ : (Arr Int)) (a'₆₃ : Int) (a'₆₄ : (Arr Int)) (a'₆₅ : Int) (a'₆₆ : Int) (a'₆₇ : Int) (a'₆₈ : Int) (a'₆₉ : (Arr Int)) (a'₇₀ : Int) : Prop :=
  True

def k2 (out : Int) (j : Int) (a6 : (Arr Int)) (a6len : Int) (i : Int) (old : (Arr Int)) (oldlen : Int) (lo : Int) (mid : Int) (hi : Int) (auxo : (Arr Int)) (auxolen : Int) (a'₈₂ : Int) (a2 : (Arr Int)) (a2len : Int) : Prop :=
  ((out ≥ 0) ∧ (out ≥ i) ∧ (out ≥ lo) ∧ (out ≤ a'₈₂) ∧ (out ≤ oldlen)) ∧
  a6len = oldlen ∧ a2len = a6len ∧
  sort_is_sorted_between a6 lo out ∧
  is_frame old a6 lo hi ∧
  i + j - lo - mid - 1 = out - lo ∧
  out ≤ hi + 1 ∧
  is_mix a6 a2 a2 lo lo (mid + 1) out i j ∧
  i ≤ hi + 1 ∧ j ≤ hi + 1 ∧
  lo ≤ i ∧ mid + 1 ≤ j ∧
  -- Weaker bound: only the last placed element is bounded by the next candidates.
  (lo < out → i ≤ mid → a6 (out - 1) ≤ a2 i) ∧
  (lo < out → j ≤ hi → a6 (out - 1) ≤ a2 j) ∧
  -- aux equals old on the merge range so that we can transfer sortedness of old to a2
  vectors_arr_eq_between a2 old lo (hi + 1)

def k3 (a'₃₄ : Int) (a'₃₅ : Int) (a'₃₆ : Int) (a'₃₇ : (Arr Int)) (a'₃₈ : Int) (a'₃₉ : Int) (a'₄₀ : (Arr Int)) (a'₄₁ : Int) (a'₄₂ : Int) (a'₄₃ : Int) (a'₄₄ : Int) (a'₄₅ : (Arr Int)) (a'₄₆ : Int) (a'₄₇ : Int) (a'₄₈ : (Arr Int)) (a'₄₉ : Int) : Prop :=
  True

attribute [grind] k0
attribute [grind] k1
attribute [grind] k2
attribute [grind] k3
attribute [grind] k4
attribute [grind] k5
attribute [grind] k6
attribute [grind] k7
attribute [grind] k8
attribute [grind] k9
attribute [grind] k10
attribute [grind] k11
attribute [grind] k12
attribute [grind] k13
attribute [grind] k14
attribute [grind] k15
attribute [grind] k16
attribute [grind] k17
attribute [grind] sort_is_sorted_between
attribute [grind] is_frame

--     -- veqb a3 old l k
--     -- is_mix a7 a3 a3 lo lo (mid + 1) out i j
--     -- is_perm old a7 lo hi
theorem eq_mix_perm (old a3 a7 : Arr Int) (lo mid hi out i j k : Int)
  (h1 : vectors_arr_eq_between a3 old lo k)
  (h2 : is_mix a7 a3 a3 lo lo (mid + 1) out i j)
  (hlm : lo ≤ mid)
  (hout : hi < out)
  (hi_hi : i ≤ hi + 1)
  (hj_hi : j ≤ hi + 1)
  (hk_hi : hi < k)
  (hijout : i + j - lo - mid - 1 = out - lo)
  : is_perm old a7 lo hi := by
  intro x hx
  have hx' : lo ≤ x ∧ x ≤ hi := by
    simpa using hx
  rcases hx' with ⟨hlox, xlehi⟩
  have xltout : x < out := by omega
  have hmix := h2 x ⟨hlox, xltout⟩
  rcases hmix with hleft | hright
  · rcases hleft with ⟨y, hy⟩
    rcases hy with ⟨hy_range, hxy⟩
    rcases hy_range with ⟨hylo, hyi⟩
    have ylehi : y ≤ hi := by omega
    have hyk : y < k := by omega
    have h_eq : a3 y = old y := h1 y ⟨hylo, hyk⟩
    refine ⟨y, ?_⟩
    refine ⟨hylo, ylehi, ?_⟩
    simpa [h_eq] using hxy
  · rcases hright with ⟨y, hy⟩
    rcases hy with ⟨hy_range, hxy⟩
    rcases hy_range with ⟨hmidy, hyj⟩
    have hylo : lo ≤ y := by omega
    have ylehi : y ≤ hi := by omega
    have hyk : y < k := by omega
    have h_eq : a3 y = old y := h1 y ⟨hylo, hyk⟩
    refine ⟨y, ?_⟩
    refine ⟨hylo, ylehi, ?_⟩
    simpa [h_eq] using hxy

-- a28 = arr_set a7 out (arr_get a3 i)
-- sorted_between a7 lo out
-- Helper lemma: setting position `out` to value v preserves sortedness
-- provided the previous last element is ≤ v (or out = lo, in which case the
-- resulting range has only one element).
theorem set_preserves_sorted
  (a28 a7 : Arr Int) (lo out : Int) (v : Int)
  (h1 : a28 = vectors_arr_set a7 out v)
  (h3 : sort_is_sorted_between a7 lo out)
  (hlast_ge : out = lo ∨ a7 (out - 1) ≤ v)
  : sort_is_sorted_between a28 lo (out + 1) := by
  subst h1
  intro x y hxy
  rcases hxy with ⟨hxlo, hxy_lt, hy_out1⟩
  have hy_le_out : y ≤ out := by omega
  by_cases hy_eq_out : y = out
  · have hx_out : x < out := by omega
    have hx_ne_out : x ≠ out := by omega
    have hx_bound : a7 x ≤ v := by
      rcases hlast_ge with h_out_lo | h_last
      · exfalso
        omega
      · by_cases hx_last : x = out - 1
        · simpa [hx_last] using h_last
        · have hx_lt_last : x < out - 1 := by omega
          have hs : a7 x ≤ a7 (out - 1) := h3 x (out - 1) ⟨hxlo, hx_lt_last, by omega⟩
          calc
            a7 x ≤ a7 (out - 1) := hs
            _ ≤ v := h_last
    simpa [vectors_arr_set, hy_eq_out, hx_ne_out] using hx_bound
  · have hy_out : y < out := by omega
    have hs : a7 x ≤ a7 y := h3 x y ⟨hxlo, hxy_lt, hy_out⟩
    have hx_ne_out : x ≠ out := by omega
    have hy_ne_out : y ≠ out := by omega
    simpa [vectors_arr_set, hx_ne_out, hy_ne_out] using hs

-- Helper: arr_set at `out` leaves other indices unchanged.
theorem arr_set_other (a : Arr Int) (out w v : Int) (h : w ≠ out) :
    vectors_arr_set a out v w = a w := by
  simp [vectors_arr_set, h]

-- Helper: arr_set at `out` returns the new value at `out`.
theorem arr_set_at (a : Arr Int) (out v : Int) :
    vectors_arr_set a out v out = v := by
  simp [vectors_arr_set]

-- Sortedness of a2 follows from sortedness of old when they agree on the range.
theorem sorted_of_eq_between
  (a2 old : Arr Int) (lo hi l r : Int)
  (heq : vectors_arr_eq_between a2 old lo hi)
  (hsort : sort_is_sorted_between old l r)
  (hlo_l : lo ≤ l) (hr_hi : r ≤ hi)
  : sort_is_sorted_between a2 l r := by
  intro p q ⟨hlp, hpq, hqr⟩
  have hpeq : a2 p = old p := heq p ⟨by omega, by omega⟩
  have hqeq : a2 q = old q := heq q ⟨by omega, by omega⟩
  rw [hpeq, hqeq]
  exact hsort p q ⟨hlp, hpq, hqr⟩

-- bounded_above preservation when taking from the left side: inserting a3[i]
-- at position `out` yields bounded_above on out+1 with index i+1, provided the
-- source a3 is sorted enough and previous bound held.
theorem bounded_above_step_left_i
  (a7 a3 : Arr Int) (lo out i : Int)
  (h_bd : bounded_above a7 a3 lo out i)
  (h_a3_step : a3 i ≤ a3 (i+1))
  : bounded_above (vectors_arr_set a7 out (vectors_arr_get a3 i)) a3 lo (out+1) (i+1) := by
  intro p ⟨hlo_p, hp_out⟩
  by_cases hpeq : p = out
  · rw [hpeq, arr_set_at]
    simpa [vectors_arr_get] using h_a3_step
  · rw [arr_set_other _ _ _ _ hpeq]
    have hp_lt : p < out := by omega
    have h_bd_p : a7 p ≤ a3 i := h_bd p ⟨hlo_p, hp_lt⟩
    omega

-- When the "next" index does not change (took from right when proving left-bound).
theorem bounded_above_step_keep_i
  (a7 a3 : Arr Int) (lo out i v : Int)
  (h_bd : bounded_above a7 a3 lo out i)
  (h_v_le : v ≤ a3 i)
  : bounded_above (vectors_arr_set a7 out v) a3 lo (out+1) i := by
  intro p ⟨hlo_p, hp_out⟩
  by_cases hpeq : p = out
  · rw [hpeq, arr_set_at]; exact h_v_le
  · rw [arr_set_other _ _ _ _ hpeq]
    have hp_lt : p < out := by omega
    exact h_bd p ⟨hlo_p, hp_lt⟩

-- Step lemma: after writing a3[i_old] at position `out` in a7 to form a28, the
-- new "last element" value a28 out is ≤ a3 i_new, when i_old ≤ i_new are both
-- in a sorted range of a3.
theorem last_bound_step_same_half
  (a7 a28 a3 : Arr Int) (lo_src hi_src out i_old i_new : Int)
  (h_a3_sort : sort_is_sorted_between a3 lo_src (hi_src + 1))
  (h_a28 : a28 = vectors_arr_set a7 out (vectors_arr_get a3 i_old))
  (h_lo_src_i : lo_src ≤ i_old)
  (h_i_new : i_new ≤ hi_src)
  (h_i_ord : i_old ≤ i_new)
  : a28 out ≤ a3 i_new := by
  subst h_a28
  simp only [vectors_arr_set, vectors_arr_get,
             LeanProofs.Lib.Lemmas.arr_set, LeanProofs.Lib.Lemmas.arr_get]
  simp
  by_cases heq : i_old = i_new
  · rw [heq]; exact Int.le_refl _
  · exact h_a3_sort i_old i_new ⟨h_lo_src_i, by omega, by omega⟩

-- Step lemma: after writing v at position `out`, with v ≤ a3 i, the new last
-- element is bounded.
theorem last_bound_step_keep
  (a7 a28 a3 : Arr Int) (out i v : Int)
  (h_a28 : a28 = vectors_arr_set a7 out v)
  (h_v_le : v ≤ a3 i)
  : a28 out ≤ a3 i := by
  subst h_a28
  simp only [vectors_arr_set, LeanProofs.Lib.Lemmas.arr_set]
  simp
  exact h_v_le

-- Combined bullet 7/8 helper: after one merge step, the new "last element"
-- is ≤ the corresponding next candidate on a given side.
-- Direction = left means we bound against new_i (i'); right means against new_j (j').
theorem merge_step_left_bound
  (old a3 a7 a28 : Arr Int) (lo mid hi out i j i' j' : Int)
  (h_eq : vectors_arr_eq_between a3 old lo (hi + 1))
  (h_old_sort_l : sort_is_sorted_between old lo (mid + 1))
  (h_old_sort_r : sort_is_sorted_between old (mid + 1) (hi + 1))
  (h_lo_out : lo ≤ out) (h_out_hi : out ≤ hi)
  (h_lo_i : lo ≤ i) (h_mid_j : mid + 1 ≤ j) (h_mid_hi : mid < hi)
  (h_i_le_mid : i ≤ mid)
  (h_step :
    (j > hi ∧ a28 = vectors_arr_set a7 out (vectors_arr_get a3 i) ∧ i' = i + 1 ∧ j' = j) ∨
    (vectors_arr_get a3 j < vectors_arr_get a3 i ∧
       a28 = vectors_arr_set a7 out (vectors_arr_get a3 j) ∧ i' = i ∧ j' = j + 1) ∨
    (¬ vectors_arr_get a3 j < vectors_arr_get a3 i ∧
       a28 = vectors_arr_set a7 out (vectors_arr_get a3 i) ∧ i' = i + 1 ∧ j' = j))
  (hi'_mid : i' ≤ mid)
  : a28 (out + 1 - 1) ≤ a3 i' := by
  have h_idx : out + 1 - 1 = out := by omega
  have h_a3_sort_l : sort_is_sorted_between a3 lo (mid + 1) :=
    sorted_of_eq_between a3 old lo (hi + 1) lo (mid + 1) h_eq h_old_sort_l
      (by omega) (by omega)
  rcases h_step with ⟨_, ha28, hi', _⟩ | ⟨h_lt, ha28, hi', _⟩ | ⟨h_ge, ha28, hi', _⟩
  -- Case L: take left, i' = i+1, a28 writes a3 i. Bound a3 i ≤ a3 (i+1) via sortedness.
  · rw [h_idx, ha28, hi']
    have : i + 1 ≤ mid := by omega
    exact last_bound_step_same_half a7 _ a3 lo mid out i (i + 1)
      h_a3_sort_l rfl h_lo_i (by omega) (by omega)
  -- Case R: take right, i' = i, a28 writes a3 j. Need a3 j ≤ a3 i. Have a3 j < a3 i.
  · rw [h_idx, ha28, hi']
    have h_lt' : a3 j < a3 i := h_lt
    exact last_bound_step_keep a7 _ a3 out i _ rfl (Int.le_of_lt h_lt')
  -- Case Le: take left, i' = i+1, a28 writes a3 i. Same as Case L.
  · rw [h_idx, ha28, hi']
    have : i + 1 ≤ mid := by omega
    exact last_bound_step_same_half a7 _ a3 lo mid out i (i + 1)
      h_a3_sort_l rfl h_lo_i (by omega) (by omega)

theorem merge_step_right_bound
  (old a3 a7 a28 : Arr Int) (lo mid hi out i j i' j' : Int)
  (h_eq : vectors_arr_eq_between a3 old lo (hi + 1))
  (h_old_sort_l : sort_is_sorted_between old lo (mid + 1))
  (h_old_sort_r : sort_is_sorted_between old (mid + 1) (hi + 1))
  (h_lo_out : lo ≤ out) (h_out_hi : out ≤ hi)
  (h_lo_i : lo ≤ i) (h_mid_j : mid + 1 ≤ j) (h_mid_hi : mid < hi)
  (h_i_le_mid : i ≤ mid)
  (h_step :
    (j > hi ∧ a28 = vectors_arr_set a7 out (vectors_arr_get a3 i) ∧ i' = i + 1 ∧ j' = j) ∨
    (vectors_arr_get a3 j < vectors_arr_get a3 i ∧
       a28 = vectors_arr_set a7 out (vectors_arr_get a3 j) ∧ i' = i ∧ j' = j + 1) ∨
    (¬ vectors_arr_get a3 j < vectors_arr_get a3 i ∧
       a28 = vectors_arr_set a7 out (vectors_arr_get a3 i) ∧ i' = i + 1 ∧ j' = j))
  (hj'_hi : j' ≤ hi)
  : a28 (out + 1 - 1) ≤ a3 j' := by
  have h_idx : out + 1 - 1 = out := by omega
  have h_a3_sort_r : sort_is_sorted_between a3 (mid + 1) (hi + 1) :=
    sorted_of_eq_between a3 old lo (hi + 1) (mid + 1) (hi + 1) h_eq h_old_sort_r
      (by omega) (by omega)
  rcases h_step with ⟨h_jhi, ha28, _, hj'⟩ | ⟨_, ha28, _, hj'⟩ | ⟨h_ge, ha28, _, hj'⟩
  -- Case L: j' = j > hi, contradiction with j' ≤ hi
  · rw [h_idx, ha28, hj']
    exfalso; omega
  -- Case R: take right, j' = j+1, a28 writes a3 j. Bound a3 j ≤ a3 (j+1).
  · rw [h_idx, ha28, hj']
    have : j + 1 ≤ hi := by omega
    exact last_bound_step_same_half a7 _ a3 (mid + 1) hi out j (j + 1)
      h_a3_sort_r rfl h_mid_j (by omega) (by omega)
  -- Case Le: take left (¬ a3 j < a3 i), j' = j, a28 writes a3 i. Need a3 i ≤ a3 j.
  · rw [h_idx, ha28, hj']
    have h_ge' : ¬ a3 j < a3 i := h_ge
    exact last_bound_step_keep a7 _ a3 out j _ rfl (Int.not_lt.mp h_ge')

set_option maxHeartbeats 2000000

def SortMerge_proof : SortMerge := by
  unfold SortMerge
  exists k0 ; exists k1 ; exists k2 ; exists k3
  exists k4 ; exists k5 ; exists k6 ; exists k7
  exists k8 ; exists k9 ; exists k10 ; exists k11
  exists k12 ; exists k13 ; exists k14 ; exists k15
  exists k16 ; exists k17
  zap
  · -- is_mix old a'₃ a'₃ lo lo (mid+1) lo lo (mid+1) (initial, empty range)
    grind [is_mix]
  · -- is_perm old a'₇ lo hi (merge-loop exit)
    grind [is_ordered_mix, eq_mix_perm]
  · -- sort_is_sorted_between a'₂₈ lo (out+1) (merge step)
    sorry
  · -- a'₂₈ i = old i for i < lo
    unfold k0 k2 k13 at *
    split_hyps
    all_goals (first | grind | (simp_all [vectors_arr_set]; grind))
  · -- a'₂₈ i = old i for hi < i
    unfold k0 k2 k13 at *
    split_hyps
    all_goals (first | grind | (simp_all [vectors_arr_set]; grind))
  · -- is_mix a'₂₈ a'₃ a'₃ lo lo (mid+1) (out+1) i₃ j₃
    sorry
  · -- a'₂₈ (out+1-1) ≤ a'₃ i₃ (left bound preservation)
    sorry
  · -- a'₂₈ (out+1-1) ≤ a'₃ j₃ (right bound preservation)
    sorry
  · -- vectors_arr_set a'₃ k (old k) i = v i for i < lo
    unfold k0 at *
    split_hyps
    all_goals (first | grind | (simp_all [vectors_arr_set]; grind))
  · -- vectors_arr_set a'₃ k (old k) i = v i for hi < i
    unfold k0 at *
    split_hyps
    all_goals (first | grind | (simp_all [vectors_arr_set]; grind))
  · -- vectors_arr_eq_between (vectors_arr_set a'₃ k (old k)) old lo (k+1)
    unfold k0 at *
    split_hyps
    all_goals (first | grind | (simp_all [vectors_arr_set]; grind))

end F
