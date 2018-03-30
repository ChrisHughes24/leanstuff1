/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/

import data.nat.basic algebra.group data.real.cau_seq tactic.ring data.nat.choose algebra.archimedean

open nat is_absolute_value
variables {α : Type*} {β : Type*}

def series [has_add α] (f : ℕ → α) : ℕ → α
| 0       := f 0
| (n + 1) := series n + f (n + 1)

def sum_between [has_add α] (f : ℕ → α) (n m : ℕ) := series (λ k, f (k + n)) (m - n)

@[simp] lemma series_zero [has_add α] (f : ℕ → α) : series f 0 = f 0 := by unfold series

lemma series_succ [has_add α] (f : ℕ → α) (n : ℕ) : series f (succ n) = series f n + f (succ n):= by unfold series

lemma series_eq_finset_sum [add_comm_monoid α] (f : ℕ → α) (n : ℕ) : series f n = finset.sum (finset.range (succ n)) f := begin
  induction n with n' hi,
  simp!,rw [finset.range_succ,series_succ],
  have : succ n' ∉ (finset.range (succ n')) := by {rw finset.mem_range,
  exact lt_irrefl _},
  rw [finset.sum_insert this,hi,add_comm],
end

lemma series_succ₁ [add_comm_monoid α] (f : ℕ → α) (i : ℕ) : series f (succ i) = f 0 + series (λ i, f (succ i)) i := begin
 induction i with i' hi,
 refl,
 rw [series_succ, hi, series_succ, add_assoc],
end

lemma series_comm [add_comm_monoid α] (f : ℕ → α) (n : ℕ) : series f n = series (λ i, f (n - i)) n := begin
  induction n with n' hi,
  simp!,simp!,rw hi,
  have : (λ (i : ℕ), f (succ n' - i)) (succ n') = f (n' - n'),simp,
  rw ←this,have : (λ (i : ℕ), f (succ n' - i)) (succ n') + series (λ (i : ℕ), f (succ n' - i)) n' = series (λ (i : ℕ), f (succ n' - i)) (succ n'),simp!,
  rw this,
  have : (λ i, f (n' - i)) = (λ i, f (succ n' - succ i)) := by
   {apply funext,assume i,rw succ_sub_succ},
  rw this,clear this,
  have : f (succ n') = (λ (i : ℕ), f (succ n' - i)) 0,simp,rw this,rw ←series_succ₁,
end

lemma series_neg [ring α] (f : ℕ → α) (n : ℕ) : -series f n = series (λ m, -f m) n := begin
  induction n with n' hi, simp!,simp![hi],
end

lemma series_sub_series [ring α] (f : ℕ → α) {i j : ℕ} : i < j → series f j - series f i 
= series (λ (k : ℕ), f (k + (i + 1))) (j - (i + 1)) := begin
  assume ij,
  induction i with i' hi,
  cases j with j',exact absurd ij dec_trivial,
  rw sub_eq_iff_eq_add',
  exact series_succ₁  _ _,
  rw [series_succ,sub_add_eq_sub_sub,hi (lt_of_succ_lt ij),sub_eq_iff_eq_add'],
  have : (j - (i' + 1)) = succ (j - (succ i' + 1)) := by
    {rw [←nat.succ_sub ij,succ_sub_succ]},
  rw this,
  have : f (succ i') = (λ (k : ℕ), f (k + (i' + 1))) 0 := by simp,
  rw this,simp[succ_add,add_succ],
  rw series_succ₁,simp,
end

lemma series_const_zero [has_zero α] (i : ℕ): series (λ j, 0) i = 0 := begin
  induction i with i' hi,simp,simpa [series_succ],
end

lemma series_add [add_comm_monoid α] (f g : ℕ → α) (n : ℕ) : series (λ i, f i + g i) n = series f n + series g n := begin
  induction n with n' hi,simp[series_zero],simp[series_succ,hi],
end

lemma series_mul_left [semiring α] (f : ℕ → α) (a : α) (n : ℕ) : series (λ i, a * f i) n = a * series f n := begin
  induction n with n' hi,simp[series_zero],simp[series_succ,hi,mul_add],
end
 
lemma series_mul_right [semiring α] (f : ℕ → α) (a : α) (n : ℕ) : series (λ i, f i * a) n = series f n * a:= begin
  induction n with n' hi,simp[series_zero],simp[series_succ,hi,add_mul],
end

lemma abv_series_le_series_abv [discrete_linear_ordered_field α] [ring β] {f : ℕ → β}
{abv : β → α} [is_absolute_value abv] (n : ℕ) : abv (series f n) ≤ series (λ i, abv (f i)) n := begin
  induction n with n' hi,
  simp,simp[series_succ],
  exact le_trans (abv_add _ _ _) (add_le_add_left hi _),
end

lemma series_mul_series [semiring α] (f g : ℕ → α) (n m : ℕ) : series f n * series g m
= series (λ i, f i * series g m) n := begin
  induction n with n' hi,
  simp,simp[series_succ,mul_add,add_mul,hi],
end

lemma series_le_series [ordered_cancel_comm_monoid α] {f g : ℕ → α} {n : ℕ} : (∀ m ≤ n, f m ≤ g m) → 
series f n ≤ series g n := begin
  assume h,induction n with n' hi,exact h 0 (le_refl _),
  unfold series,exact add_le_add (hi (λ m hm, h m (le_succ_of_le hm))) (h _ (le_refl _)),
end

lemma series_lt_series [ordered_cancel_comm_monoid α] {f g : ℕ → α} {n : ℕ} : (∀ m ≤ n, f m < g m) → 
series f n < series g n := begin
  assume h,induction n with n' hi,exact h 0 (le_refl _),
  unfold series,exact add_lt_add (hi (λ m hm, h m (le_succ_of_le hm))) (h _ (le_refl _)),
end

lemma series_congr [has_add α] {f g : ℕ → α} {i : ℕ} : (∀ j ≤ i, f j = g j) → series f i = series g i := begin
  assume h,induction i with i' hi,exact h 0 (zero_le _),
  unfold series,rw h _ (le_refl (succ i')),
  rw hi (λ j ji, h j (le_succ_of_le ji)),
end

lemma series_nonneg [ordered_cancel_comm_monoid α] {f : ℕ → α} {n : ℕ} : (∀ m ≤ n, 0 ≤ f m) → 0 ≤ series f n := begin
  induction n with n' hi,simp,assume h,exact h 0 (le_refl _),
  assume h,unfold series,refine add_nonneg (hi (λ m hm, h m (le_succ_of_le hm))) (h _ (le_refl _)),
end

lemma series_pos [ordered_cancel_comm_monoid α] {f : ℕ → α} {n : ℕ} : (∀ m ≤ n, 0 < f m) → 0 < series f n := begin
  induction n with n' hi,simp,assume h,exact h 0 (le_refl _),
  assume h,unfold series,refine add_pos (hi (λ m hm, h m (le_succ_of_le hm))) (h _ (le_refl _)),
end

-- proof that two different ways of representing a sum across a 2D plane are equal, used
-- in proof of exp (x + y) = exp x * exp y
lemma series_series_diag_flip [add_comm_monoid α] (f : ℕ → ℕ → α) (n : ℕ) : series (λ i, 
series (λ k, f k (i - k)) i) n = series (λ i, series (λ k, f i k) (n - i)) n := begin
  have : ∀ m : ℕ, m ≤ n → series (λ (i : ℕ), series (λ k, f k (i - k)) (min m i)) n =
  series (λ i, series (λ k, f i k) (n - i)) m := by
  { assume m mn, induction m with m' hi,
    simp[series_succ,series_zero,mul_add,max_eq_left (zero_le n)],
    simp only [series_succ _ m'],rw ←hi (le_of_succ_le mn),clear hi,
    induction n with n' hi,
    simp[series_succ],exact absurd mn dec_trivial,cases n' with n₂,
    simp [series_succ],rw [min_eq_left mn,series_succ,min_eq_left (le_of_succ_le mn)],
    rw eq_zero_of_le_zero (le_of_succ_le_succ mn),simp,
    cases lt_or_eq_of_le mn,
    simp [series_succ _ (succ n₂),min_eq_left mn,hi (le_of_lt_succ h)],rw [←add_assoc,←add_assoc],
    suffices : series (f (succ m')) (n₂ - m') + series (λ (k : ℕ), f k (succ (succ n₂) - k)) (succ m')
    = series (f (succ m')) (succ n₂ - m') +
        series (λ (k : ℕ), f k (succ (succ n₂) - k)) (min m' (succ (succ n₂))),
      rw this,rw[min_eq_left (le_of_succ_le mn),series_succ,succ_sub_succ,succ_sub (le_of_succ_le_succ (le_of_lt_succ h)),series_succ],
      rw [add_comm (series (λ (k : ℕ), f k (succ (succ n₂) - k)) m'),add_assoc],      
    rw ←h,simp[nat.sub_self],clear hi mn h,simp[series_succ,nat.sub_self],
    suffices : series (λ (i : ℕ), series (λ (k : ℕ), f k (i - k)) (min (succ m') i)) m' = series (λ (i : ℕ), series (λ (k : ℕ), f k (i - k)) (min m' i)) m',
      rw [this,min_eq_left (le_succ _)],clear n₂,
    have h₁ : ∀ i ≤ m', (λ (i : ℕ), series (λ (k : ℕ), f k (i - k)) (min (succ m') i)) i = (λ (i : ℕ), series (λ (k : ℕ), f k (i - k)) (min m' i)) i,
      assume i im,simp, rw [min_eq_right im,min_eq_right (le_succ_of_le im)],
    rw series_congr h₁},
  specialize this n (le_refl _),
  rw ←this,refine series_congr _,assume i ni,rw min_eq_right ni,
end

open monoid

theorem series_binomial {α : Type*} [comm_semiring α] (x y : α) (i : ℕ) : pow (x + y) i = 
series (λ j, choose i j * pow x j * pow y (i - j)) i := begin
  induction i with i' hi,
  simp!,unfold monoid.pow,rw hi,
  rw [←series_mul_left],
  have : ∀ j : ℕ, j ≤ i' → (λ (i : ℕ), (x + y) * (↑(choose i' i) * pow x i * pow y (i' - i))) j
  = choose i' j * pow x (succ j) * pow y (i' - j) + choose i' j * pow x j * pow y (succ i' - j) := by
  { assume j ji,dsimp only,rw add_mul,
    have :  x * (↑(choose i' j) * pow x j * pow y (i' - j)) + y * (↑(choose i' j) * pow x j * pow y (i' - j))
    = ↑(choose i' j) * (x * pow x j) * pow y (i' - j) + ↑(choose i' j) * pow x j * (y * pow y (i' - j)),
      simp[mul_comm,_root_.mul_assoc,mul_left_comm],
    rw [this,←_root_.pow_succ,←_root_.pow_succ,succ_sub ji]},
  rw [series_congr this],clear this, 
  clear hi,rw series_add,
  have : series (λ (i : ℕ), ↑(choose i' i) * pow x i * pow y (succ i' - i)) i' = 
      series (λ (i : ℕ), ↑(choose i' i) * pow x i * pow y (succ i' - i)) (succ i') := by
  { simp[series_succ],},
  rw [this,series_succ₁,series_succ₁],
  simp[nat.sub_self],rw ←series_add,
  refine congr_arg _ (series_congr _),
  assume j ji,unfold choose,rw [nat.cast_add,add_mul,add_mul],
end

lemma geo_series_eq {α : Type*} [field α] (x : α) (n : ℕ) : x ≠ 1 → series (pow x) n = (1 - pow x (succ n)) / (1 - x) := begin
  assume x1,have x1' : 1 + -x ≠ 0,assume h,rw [eq_comm, ←sub_eq_iff_eq_add] at h,simp at h,trivial,
  induction n with n' hi,
  {simp![div_self x1']},
  {rw eq_div_iff_mul_eq,simpa,
  rw [_root_.series_succ,_root_.pow_succ _ (succ n')],
  rw hi,simp,rw [add_mul,div_mul_cancel _ x1',mul_add],ring,exact x1'},
end

lemma is_cau_geo_series {α : Type*} [discrete_linear_ordered_field α] [archimedean α] (x : α) : 
abs x < 1 → is_cau_seq abs (series (pow x)) := begin
  assume x1, have : series (pow x) = λ n,(1 - pow x (succ n)) / (1 - x),
    apply funext,assume n,refine geo_series_eq x n _ ,assume h, rw h at x1,exact absurd x1 (by norm_num),rw this,
  have absx : 0 < abs (1 - x),refine abs_pos_of_ne_zero _,assume h,rw sub_eq_zero_iff_eq at h,rw ←h at x1,
  have : ¬abs (1 : α) < 1,norm_num,trivial,simp at absx,
  cases classical.em (x = 0),rw h,simp[monoid.pow],assume ε ε0,existsi 1,assume j j1,simpa!,
  have x2: 1 < (abs x)⁻¹,rw lt_inv,simpa,{norm_num},exact abs_pos_of_ne_zero h,
  have pos_x : 0 < abs x := abs_pos_of_ne_zero h,
  assume ε ε0,
  cases pow_unbounded_of_gt_one (2 / (ε * abs (1 - x))) x2 with i hi,
  have ε2 : 0 < 2 / (ε * abs (1 - x)) := div_pos (by norm_num) (mul_pos ε0 absx),
  rw [pow_inv,lt_inv ε2 (pow_pos pos_x _)] at hi,
  existsi i,assume j ji,rw [inv_eq_one_div,div_div_eq_mul_div,_root_.one_mul,lt_div_iff (by norm_num : (0 : α) < 2)] at hi,
  rw [div_sub_div_same,abs_div,div_lt_iff absx],
  refine lt_of_le_of_lt _ hi,
  simp,
  refine le_trans (abs_add _ _) _,
  have : pow (abs x) i * 2 = pow (abs x) i + pow (abs x) i,ring,
  rw this,
  refine add_le_add _ _,
  {rw [←_root_.one_mul (pow (abs x) i),pow_abs,_root_.pow_succ,abs_mul],
  exact mul_le_mul_of_nonneg_right (le_of_lt x1) (abs_nonneg _)},
  {rw [abs_neg,←pow_abs],
  rw [←inv_le_inv (pow_pos pos_x _) (pow_pos pos_x _),←pow_inv,←pow_inv],
  refine pow_le_pow (le_of_lt x2) (le_succ_of_le ji),}
end

lemma is_cau_geo_series_const {α : Type*} [discrete_linear_ordered_field α] [archimedean α] (a x : α) :
abs x < 1 → is_cau_seq abs (series (λ n, a * pow x n)) := begin
  assume x1 ε ε0,
  cases classical.em (a = 0),
  existsi 0,intros,rw [series_mul_left],induction j,simp!,assumption,rw h,simpa!,
  cases is_cau_geo_series x x1 (ε / abs a) (div_pos ε0 (abs_pos_of_ne_zero h)) with i hi,
  existsi i,assume j ji,rw [series_mul_left,series_mul_left,←mul_sub,abs_mul,mul_comm,←lt_div_iff],
  exact hi j ji,exact abs_pos_of_ne_zero h,
end

lemma is_cau_series_of_abv_le_cau {α : Type*} {β : Type*} [discrete_linear_ordered_field α] [ring β] {f : ℕ → β}
{g : ℕ → α} {abv : β → α} [is_absolute_value abv] (n : ℕ) : (∀ m, n ≤ m → abv (f m) ≤ g m) → 
is_cau_seq abs (series g) → is_cau_seq abv (series f) := begin
  assume hm hg ε ε0,cases hg (ε / 2) (div_pos ε0 (by norm_num)) with i hi,
  existsi max n i,
  assume j ji,
  have hi₁ := hi j (le_trans (le_max_right n i) ji),
  have hi₂ := hi (max n i) (le_max_right n i),
  have sub_le := abs_sub_le (series g j) (series g i) (series g (max n i)),
  have := add_lt_add hi₁ hi₂,rw abs_sub (series g (max n i)) at this,
  have ε2 : ε / 2 + ε / 2 = ε,ring,
  rw ε2 at this,
  refine lt_of_le_of_lt _ this,
  refine le_trans _ sub_le,
  refine le_trans _ (le_abs_self _),
  generalize hk : j - max n i = k,clear this ε2 hi₂ hi₁ hi ε0 ε hg sub_le,
  rw nat.sub_eq_iff_eq_add ji at hk,rw hk, clear hk ji j,
  induction k with k' hi,simp,rw abv_zero abv,
  rw succ_add,unfold series,
  rw [add_comm,add_sub_assoc],
  refine le_trans (abv_add _ _ _) _,
  rw [add_comm (series g (k' + max n i)),add_sub_assoc],
  refine add_le_add _ _,
  refine hm _ _,rw [←zero_add n,←succ_add],refine add_le_add _ _,exact zero_le _,
  simp, exact le_max_left _ _,assumption,
end

-- The form of ratio test with  0 ≤ r < 1, and abv (f (succ m)) ≤ r * abv (f m) handled zero terms of series the best
lemma series_ratio_test {α : Type*} {β : Type*} [discrete_linear_ordered_field α] [ring β] 
[archimedean α] {abv : β → α} [is_absolute_value abv] {f : ℕ → β} (n : ℕ) (r : α) :
0 ≤ r → r < 1 → (∀ m, n ≤ m → abv (f (succ m)) ≤ r * abv (f m)) → is_cau_seq abv (series f)
  := begin
  assume r0 r1 h,
  refine is_cau_series_of_abv_le_cau (succ n) _ (is_cau_geo_series_const (abv (f (succ n)) * pow r⁻¹ (succ n)) r _),
  assume m mn,
  generalize hk : m - (succ n) = k,rw nat.sub_eq_iff_eq_add mn at hk,
  cases classical.em (r = 0) with r_zero r_pos,have m_pos := lt_of_lt_of_le (succ_pos n) mn,
  have := pred_le_pred mn,simp at this,
  have := h (pred m) this,simp[r_zero,succ_pred_eq_of_pos m_pos] at this,
  refine le_trans this _,refine mul_nonneg _ _,refine mul_nonneg (abv_nonneg _ _) (pow_nonneg (inv_nonneg.mpr r0) _),exact pow_nonneg r0 _,
  replace r_pos : 0 < r,cases lt_or_eq_of_le r0 with h h,exact h,exact absurd h.symm r_pos,
  revert m n,
  induction k with k' hi,assume m n h mn hk,
  rw [hk,zero_add,mul_right_comm,←pow_inv _ _ (ne_of_lt r_pos).symm,←div_eq_mul_inv,mul_div_cancel],
  exact (ne_of_lt (pow_pos r_pos _)).symm,
  assume m n h mn hk,rw [hk,succ_add],
  have kn : k' + (succ n) ≥ (succ n), rw ←zero_add (succ n),refine add_le_add _ _,exact zero_le _,simp,
  replace hi := hi (k' + (succ n)) n h kn rfl,
  rw [(by simp!;ring : pow r (succ (k' + succ n)) = pow r (k' + succ n) * r),←_root_.mul_assoc],
  replace h := h (k' + succ n) (le_of_succ_le kn),rw mul_comm at h,
  exact le_trans h (mul_le_mul_of_nonneg_right hi r0),
  rwa abs_of_nonneg r0,
end

lemma series_cau_of_abv_cau {α : Type*} {β : Type*} [discrete_linear_ordered_field α] [ring β] {abv : β → α} {f : ℕ → β} 
[is_absolute_value abv] : is_cau_seq abs (series (λ n, abv (f n))) → is_cau_seq abv (series f) := 
   λ h, is_cau_series_of_abv_le_cau 0 (λ n h, le_refl _) h

-- I did not use the equivalent function on cauchy sequences as I do not have a proof 
-- series (λ n, series (λ m, a m * b (n - m)) n) j) is a cauchy sequence. Using this lemma
-- and of_near, this can be proven to be a cauchy sequence
lemma series_cauchy_prod {α β : Type*} [discrete_linear_ordered_field α] [ring β] {a b : ℕ → β}
{abv : β → α} [is_absolute_value abv] : is_cau_seq abs (series (λ n, abv (a n))) → is_cau_seq abv (series b) → 
∀ ε : α, 0 < ε → ∃ i : ℕ, ∀ j ≥ i, abv (series a j * series b j - series (λ n, 
series (λ m, a m * b (n - m)) n) j) < ε := begin
-- slightly adapted version of theorem 9.4.7 from "The Real Numbers and Real Analysis", Ethan D. Bloch
  assume ha hb ε ε0,
  cases cau_seq.bounded ⟨_, hb⟩ with Q hQ,simp at hQ,
  cases cau_seq.bounded ⟨_, ha⟩ with P hP,simp at hP,
  have P0 : 0 < P,exact lt_of_le_of_lt (abs_nonneg _) (hP 0),
  have Pε0 := div_pos ε0 (mul_pos (show (2 : α) > 0, from by norm_num) P0),
  cases cau_seq.cauchy₂ ⟨_, hb⟩ Pε0 with N hN,simp at hN,
  have Qε0 := div_pos ε0 (mul_pos (show (4 : α) > 0, from by norm_num) (lt_of_le_of_lt (abv_nonneg _ _) (hQ 0))),
  cases cau_seq.cauchy₂ ⟨_, ha⟩ Qε0 with M hM,simp at hM,
  existsi 2 * (max N M + 1),
  assume K hK,have := series_series_diag_flip (λ m n, a m * b n) K,simp at this,rw this,clear this,
  have : (λ (i : ℕ), series (λ (k : ℕ), a i * b k) (K - i)) = (λ (i : ℕ), a i * series (λ (k : ℕ), b k) (K - i)) := by
    {apply funext,assume i,rw series_mul_left},
  rw this,clear this,simp,
  have : series (λ (i : ℕ), a i * series b (K - i)) K = series (λ (i : ℕ), a i * (series b (K - i) - series b K))
  K + series (λ i, a i * series b K) K,
    {rw ←series_add,simp[(mul_add _ _ _).symm]},
  rw this, clear this,
  rw series_mul_series,simp,
  rw abv_neg abv,
  refine lt_of_le_of_lt (abv_series_le_series_abv _) _,
  simp [abv_mul abv],
  suffices : series (λ (i : ℕ), abv (a i) * abv (series b (K - i) + -series b K)) (max N M + 1) + 
  (series (λ (i : ℕ), abv (a i) * abv (series b (K - i) + -series b K)) K -series (λ (i : ℕ), 
  abv (a i) * abv (series b (K - i) + -series b K)) (max N M + 1)) < ε / (2 * P) * P + ε / (4 * Q) * (2 * Q),
  { simp [(div_div_eq_div_mul _ _ _).symm] at this,
    rwa[div_mul_cancel _ (ne_of_lt P0).symm,(by norm_num : (4 : α) = 2 * 2),←div_div_eq_div_mul,mul_comm (2 : α),←_root_.mul_assoc,
    div_mul_cancel _ (ne_of_lt (lt_of_le_of_lt (abv_nonneg _ _) (hQ 0))).symm,div_mul_cancel,add_halves] at this,
    norm_num},
  refine add_lt_add _ _,
  {have : series (λ (i : ℕ), abv (a i) * abv (series b (K - i) + -series b K)) (max N M + 1) ≤ series
  (λ (i : ℕ), abv (a i) * (ε / (2 * P))) (max N M + 1) := by
    {refine series_le_series _,assume m mJ,refine mul_le_mul_of_nonneg_left _ _,
      {refine le_of_lt (hN (K - m) K _ _),{
      refine nat.le_sub_left_of_add_le (le_trans _ hK),
      rw[succ_mul,_root_.one_mul],
      exact add_le_add mJ (le_trans (le_max_left _ _) (le_of_lt (lt_add_one _)))},
      {refine le_trans _ hK,rw ←_root_.one_mul N,
      refine mul_le_mul (by norm_num) (by rw _root_.one_mul;exact le_trans (le_max_left _ _) 
      (le_of_lt (lt_add_one _))) (zero_le _) (zero_le _)}},
      exact abv_nonneg abv _},
  refine lt_of_le_of_lt this _,
  rw [series_mul_right,mul_comm],
  specialize hP (max N M + 1),rwa abs_of_nonneg at hP,
  exact (mul_lt_mul_left Pε0).mpr hP,
  exact series_nonneg (λ x h, abv_nonneg abv _)},
  {have hNMK : max N M + 1 < K := by
    {refine lt_of_lt_of_le _ hK,
    rw [succ_mul,_root_.one_mul,←add_zero (max N M + 1)],
    refine add_lt_add_of_le_of_lt (le_refl _) _,rw add_zero,
    refine add_pos_of_nonneg_of_pos (zero_le _) (by norm_num)},
  rw series_sub_series _ hNMK,
  have : series (λ (k : ℕ), abv (a (k + (max N M + 1 + 1))) * abv 
  (series b (K - (k + (max N M + 1 + 1))) + -series b K)) (K - (max N M + 1 + 1)) ≤
  series (λ (k : ℕ), abv (a (k + (max N M + 1 + 1))) * (2 * Q)) (K - (max N M + 1 + 1)) := by
    {refine series_le_series _,
    assume m hm,
    refine mul_le_mul_of_nonneg_left _ _,
    {refine le_trans (abv_add abv _ _) _,
    rw (by ring : 2 * Q = Q + Q),
    refine add_le_add (le_of_lt (hQ _)) _,
    rw abv_neg abv, exact le_of_lt (hQ _)},
    exact abv_nonneg abv _},
  refine lt_of_le_of_lt this _,
  rw [series_mul_right],
  refine (mul_lt_mul_right (mul_pos (by norm_num) (lt_of_le_of_lt (abv_nonneg abv _) (hQ 0)))).mpr _,
  refine lt_of_le_of_lt (le_abs_self _) _,
  rw[←@series_sub_series _ _ (λ k, abv (a k)) (max N M + 1) K hNMK],
  refine hM _ _ _ (le_trans (le_max_right _ _) (le_of_lt (lt_add_one _))),
  refine le_trans _ hK,
  rw [succ_mul,_root_.one_mul,←add_zero M],
  exact add_le_add (le_trans (le_max_right _ _) (le_of_lt (lt_add_one _))) (zero_le _)},
end
