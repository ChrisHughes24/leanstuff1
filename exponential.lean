import data.complex.basic data.real.cau_seq tactic.norm_num data.nat.basic tactic.ring algebra.archimedean .series .limits
section a
open real nat is_absolute_value
noncomputable theory
local attribute [instance, priority 0] classical.prop_decidable

lemma pow_inv' {α : Type*} [discrete_field α] (a : α) (n : ℕ) : (monoid.pow a n)⁻¹ = monoid.pow a⁻¹ n := begin
  induction n with n' hi,
  simp!,
  simp!,rw [mul_inv',mul_comm,hi],
end

lemma pow_abs {α : Type*} [decidable_linear_ordered_comm_ring α] (a : α) (n : ℕ) : monoid.pow (abs a) n = abs (monoid.pow a n) := begin
  induction n with n' hi,
  simp!, simp!,rw [hi,abs_mul],
end

lemma pow_incrs_of_gt_one {α : Type*}  [linear_ordered_semiring α] {x : α} {n m : ℕ} : 1 < x → n < m → monoid.pow x n < monoid.pow x m := begin
  assume x1 nm,revert n,
  induction m with m' hi,assume n nm,
  {exact absurd nm (not_lt_of_ge (zero_le n))},
  assume n nm,
  cases m' with m'',
  {rw eq_zero_of_le_zero (le_of_lt_succ nm),simpa!,},
  cases n with n',
  {simp!, simp! at hi,
  rw ←one_mul (1 : α),
  exact mul_lt_mul x1 (le_of_lt (@hi 0 dec_trivial)) (by norm_num) (le_of_lt(lt_trans (by norm_num) x1))},
  {have hi' := @hi n' (lt_of_succ_lt_succ nm),
  suffices : x * monoid.pow x n' < x * monoid.pow x (succ m''),
    simpa [monoid.pow],
  refine mul_lt_mul' (le_refl x) hi' _ (lt_trans (by norm_num) x1),
  clear hi hi' nm m'',
  induction n' with n'' hi,
  simp!,norm_num,
  simp!,exact mul_nonneg (le_of_lt (lt_trans (by norm_num) x1)) hi},
end

lemma pow_dcrs_of_lt_one_of_pos {α : Type*}  [discrete_linear_ordered_field α] {x : α} {n m : ℕ} : x < 1 → 0 < x → n < m → monoid.pow x m < monoid.pow x n := begin
  assume x1 x0 nm,rw [←inv_lt_inv,pow_inv',pow_inv'],
  have x11 : 1 < x⁻¹ ,rw lt_inv,simpa,{norm_num},exact x0,
  exact pow_incrs_of_gt_one x11 nm,
  exact pow_pos x0 _,exact pow_pos x0 _,
end

lemma pow_unbounded_of_gt_one {α : Type*} [discrete_linear_ordered_field α] [archimedean α] {x : α} (y : α) : 1 < x → ∃ n : ℕ, y < monoid.pow x n := begin
  assume x1,
  have : ∀ m : ℕ, (x - 1) * m < monoid.pow x m ∧ 1 ≤ monoid.pow x m,
    assume m, induction m with m' hi,
    simp,{norm_num},
    rw [←add_one,nat.cast_add,nat.cast_one], simp only [mul_add,monoid.pow],rw mul_one,
    have : x * monoid.pow x m' = monoid.pow x m' + (x - 1) * monoid.pow x m',
      rw add_comm,simp[mul_add,add_mul],
    rw this,split,
    refine add_lt_add_of_lt_of_le hi.left _,rw ←sub_pos at x1,
    have :=mul_le_mul (le_refl (x - 1)) hi.right (by norm_num) (le_of_lt x1),rwa mul_one at this,
    rw [←this, ←one_mul (1 : α)],
    exact mul_le_mul (le_of_lt x1) hi.right (by norm_num) (le_of_lt (lt_trans (by norm_num) x1)),
  cases exists_nat_gt (y / (x - 1)) with n hn,
  existsi n,rw [div_lt_iff,mul_comm] at hn,
  exact lt_trans hn (this n).left,rwa sub_pos,
end

lemma geo_series_eq {α : Type*} [field α] (x : α) (n : ℕ) : x ≠ 1 → series (monoid.pow x) n = (1 - monoid.pow x (succ n)) / (1 - x) := begin
  assume x1,have x1' : 1 + -x ≠ 0,assume h,rw [eq_comm, ←sub_eq_iff_eq_add] at h,simp at h,trivial,
  induction n with n' hi,
  simp![div_self x1'],rw eq_div_iff_mul_eq,simpa,
  rw [_root_.series_succ,_root_.pow_succ _ (succ n')],
  rw hi,simp,rw [add_mul,div_mul_cancel _ x1',mul_add],ring,exact x1',
end

lemma geo_series_cau {α : Type*} [discrete_linear_ordered_field α] [archimedean α] (x : α) : abs x < 1 → is_cau_seq abs (series (monoid.pow x)) := begin
  assume x1, have : series (monoid.pow x) = λ n,(1 - monoid.pow x (succ n)) / (1 - x),
    apply funext,assume n,refine geo_series_eq x n _ ,assume h, rw h at x1,exact absurd x1 (by norm_num),rw this,
  have absx : 0 < abs (1 - x),refine abs_pos_of_ne_zero _,assume h,rw sub_eq_zero_iff_eq at h,rw ←h at x1,
  have : ¬abs (1 : α) < 1,norm_num,trivial,simp at absx,
  cases classical.em (x = 0),rw h,simp[monoid.pow],assume ε ε0,existsi 1,assume j j1,simpa!,
  have x2: 1 < (abs x)⁻¹,rw lt_inv,simpa,{norm_num},exact abs_pos_of_ne_zero h,
  have pos_x : 0 < abs x := abs_pos_of_ne_zero h,
  assume ε ε0,cases pow_unbounded_of_gt_one (2 / (ε * abs (1 - x))) x2 with i hi,
  have ε2 : 0 < 2 / (ε * abs (1 - x)) := div_pos (by norm_num) (mul_pos ε0 absx),
  rw [←pow_inv',lt_inv ε2 (pow_pos pos_x _)] at hi,
  existsi i,assume j ji,rw [inv_eq_one_div,div_div_eq_mul_div,one_mul,lt_div_iff (by norm_num : (0 : α) < 2)] at hi,
  rw [div_sub_div_same,abs_div,div_lt_iff absx],
  refine lt_of_le_of_lt _ hi,
  simp,
  refine le_trans (abs_add _ _) _,
  have : monoid.pow (abs x) i * 2 = monoid.pow (abs x) i + monoid.pow (abs x) i,ring,
  rw this,
  refine add_le_add _ _,
  {rw [←one_mul (monoid.pow (abs x) i),pow_abs,_root_.pow_succ,abs_mul],
  exact mul_le_mul_of_nonneg_right (le_of_lt x1) (abs_nonneg _)},
  {rw [abs_neg,←pow_abs],
  refine le_of_lt (pow_dcrs_of_lt_one_of_pos x1 pos_x (lt_succ_of_le ji))},
end

lemma geo_series_const_cau {α : Type*} [discrete_linear_ordered_field α] [archimedean α] (a x : α) : abs x < 1 → is_cau_seq abs (series (λ n, a * monoid.pow x n)) := begin
  assume x1 ε ε0,
  cases classical.em (a = 0),
  existsi 0,intros,rw [series_mul_left],induction j,simp!,assumption,rw h,simpa!,
  cases geo_series_cau x x1 (ε / abs a) (div_pos ε0 (abs_pos_of_ne_zero h)) with i hi,
  existsi i,assume j ji,rw [series_mul_left,series_mul_left,←mul_sub,abs_mul,mul_comm,←lt_div_iff],exact hi j ji,exact abs_pos_of_ne_zero h,
end

lemma series_cau_of_abv_le_cau {α : Type*} {β : Type*} [discrete_linear_ordered_field α] [ring β] {f : ℕ → β}
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
lemma series_ratio_test {α : Type*} {β : Type*} [discrete_linear_ordered_field α]  [ring β] 
    [archimedean α] {abv : β → α} [is_absolute_value abv] {f : ℕ → β} (n : ℕ) (r : α) :
    0 ≤ r → r < 1 → (∀ m, n ≤ m → abv (f (succ m)) ≤ r * abv (f m)) → is_cau_seq abv (series f)
  := begin
  assume r0 r1 h,
  refine series_cau_of_abv_le_cau (succ n) _ (geo_series_const_cau (abv (f (succ n)) * monoid.pow r⁻¹ (succ n)) r _),
  assume m mn,
  generalize hk : m - (succ n) = k,rw nat.sub_eq_iff_eq_add mn at hk,
  cases classical.em (r = 0) with r_zero r_pos,have m_pos := lt_of_lt_of_le (succ_pos n) mn,
  have := pred_le_pred mn,simp at this,
  have := h (pred m) this,simp[r_zero,succ_pred_eq_of_pos m_pos] at this,
  refine le_trans this _,refine mul_nonneg _ _,refine mul_nonneg (abv_nonneg _ _) (pow_nonneg (inv_nonneg.mpr r0) _),exact pow_nonneg r0 _,
  replace r_pos : 0 < r,cases lt_or_eq_of_le r0 with h h,exact h,exact absurd h.symm r_pos,
  revert m n,
  induction k with k' hi,assume m n h mn hk,
  rw [hk,zero_add,mul_right_comm,←pow_inv',←div_eq_mul_inv,mul_div_cancel],
  exact (ne_of_lt (pow_pos r_pos _)).symm,
  assume m n h mn hk,rw [hk,succ_add],
  have kn : k' + (succ n) ≥ (succ n), rw ←zero_add (succ n),refine add_le_add _ _,exact zero_le _,simp,
  replace hi := hi (k' + (succ n)) n h kn rfl,
  rw [(by simp!;ring : monoid.pow r (succ (k' + succ n)) = monoid.pow r (k' + succ n) * r),←mul_assoc],
  replace h := h (k' + succ n) (le_of_succ_le kn),rw mul_comm at h,
  exact le_trans h (mul_le_mul_of_nonneg_right hi r0),
  rwa abs_of_nonneg r0,
end
lemma series_cau_of_abv_cau {α : Type*} {β : Type*} [discrete_linear_ordered_field α] [ring β] {abv : β → α} {f : ℕ → β} 
    [is_absolute_value abv] : is_cau_seq abs (series (λ n, abv (f n))) → is_cau_seq abv (series f) := 
   λ h, series_cau_of_abv_le_cau 0 (λ n h, le_refl _) h

lemma series_cauchy_prod {α β : Type*} [discrete_linear_ordered_field α] [ring β] {a b : ℕ → β}
{abv : β → α} [is_absolute_value abv] : is_cau_seq abs (series (λ n, abv (a n))) → is_cau_seq abv (series b) → 
∀ ε : α, 0 < ε → ∃ i : ℕ, ∀ j ≥ i, abv (series a j * series b j - series (λ n, 
series (λ m, a m * b (n - m)) n) j) < ε := begin
  assume ha hb ε ε0,
  cases seq_bounded_above_of_cau hb with Q hQ,
  cases seq_bounded_above_of_cau ha with P hP,
  have P0 : 0 < P,exact lt_of_le_of_lt (abs_nonneg _) (hP 0),
  have Pε0 := div_pos ε0 (mul_pos (show (2 : α) > 0, from by norm_num) P0),
  cases cau_seq.cauchy₂ ⟨_, hb⟩ Pε0 with N hN,simp at hN,
  have Qε0 := div_pos ε0 (mul_pos (show (4 : α) > 0, from by norm_num) (lt_of_le_of_lt (abv_nonneg _ _) (hQ 0))),
  cases cau_seq.cauchy₂ ⟨_, ha⟩ Qε0 with M hM,simp at hM,
  existsi 2 * (max N M + 1),
  assume K hK,have := series_series_diag_flip (λ m n, a m * b n) K,simp at this,rw this,clear this,
  have : (λ (i : ℕ), series (λ (k : ℕ), a i * b k) (K - i)) = (λ (i : ℕ), a i * series (λ (k : ℕ), b k) (K - i)),
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
    rwa[div_mul_cancel _ (ne_of_lt P0).symm,(by norm_num : (4 : α) = 2 * 2),←div_div_eq_div_mul,mul_comm (2 : α),←mul_assoc,
    div_mul_cancel _ (ne_of_lt (lt_of_le_of_lt (abv_nonneg _ _) (hQ 0))).symm,div_mul_cancel,add_halves] at this,
    norm_num},
  refine add_lt_add _ _,
  {have : series (λ (i : ℕ), abv (a i) * abv (series b (K - i) + -series b K)) (max N M + 1) ≤ series
  (λ (i : ℕ), abv (a i) * (ε / (2 * P))) (max N M + 1),
    {refine series_le_series _,assume m mJ,refine mul_le_mul_of_nonneg_left _ _,
      {refine le_of_lt (hN (K - m) K _ _),{
      refine nat.le_sub_left_of_add_le (le_trans _ hK),
      rw[succ_mul,one_mul],
      exact add_le_add mJ (le_trans (le_max_left _ _) (le_of_lt (lt_add_one _)))},
      {refine le_trans _ hK,rw ←one_mul N,
      refine mul_le_mul (by norm_num) (by rw one_mul;exact le_trans (le_max_left _ _) 
      (le_of_lt (lt_add_one _))) (zero_le _) (zero_le _)}},
      exact abv_nonneg abv _},
  refine lt_of_le_of_lt this _,
  rw [series_mul_right,mul_comm],
  specialize hP (max N M + 1),rwa abs_of_nonneg at hP,
  refine (mul_lt_mul_left Pε0).mpr hP,
  refine series_nonneg _,assume x h,exact abv_nonneg abv _},
  {have hNMK : max N M + 1 < K,
    {refine lt_of_lt_of_le _ hK,
    rw [succ_mul,one_mul,←add_zero (max N M + 1)],
    refine add_lt_add_of_le_of_lt (le_refl _) _,rw add_zero,
    refine add_pos_of_nonneg_of_pos (zero_le _) (by norm_num)},
  rw series_sub_series _ hNMK,
  have : nat.sum (λ (i : ℕ), abv (a i) * abv (series b (K - i) + -series b K)) (max N M + 2) K 
  ≤ nat.sum (λ (i : ℕ), abv (a i) * (2 * Q)) (max N M + 2) K,
    {unfold nat.sum,refine series_le_series _,
    assume m hm,
    refine mul_le_mul_of_nonneg_left _ _,
    {refine le_trans (abv_add abv _ _) _,
    rw ←(by ring : Q + Q = 2 * Q),
    refine add_le_add (le_of_lt (hQ _)) _,
    rw abv_neg abv, exact le_of_lt (hQ _)},
    exact abv_nonneg abv _},
  refine lt_of_le_of_lt this _,
  rw [←series_sub_series _ hNMK,series_mul_right,series_mul_right,←sub_mul],
  refine (mul_lt_mul_right (mul_pos (by norm_num) (lt_of_le_of_lt (abv_nonneg abv _) (hQ 0)))).mpr _,
  refine lt_of_le_of_lt (le_abs_self _) _,
  refine hM _ _ _ (le_trans (le_max_right _ _) (le_of_lt (lt_add_one _))),
  refine le_trans _ hK,
  rw [succ_mul,one_mul,←add_zero M],
  exact add_le_add (le_trans (le_max_right _ _) (le_of_lt (lt_add_one _))) (zero_le _)},
end
#print axioms series_cauchy_prod
end a
open nat
lemma complex.exp_series_abs_cau (z : ℂ) : is_cau_seq abs (series (λ m, complex.abs( monoid.pow z m / fact m))) := begin
  cases exists_nat_gt (complex.abs z) with n hn,
  have n_pos : (0 : ℝ) < n := lt_of_le_of_lt (complex.abs_nonneg _) hn,
  refine series_ratio_test n (complex.abs z / n) _ _ _,exact div_nonneg_of_nonneg_of_pos (complex.abs_nonneg _) n_pos,rwa [div_lt_iff n_pos,one_mul],
  assume m mn,rw [abs_of_nonneg (complex.abs_nonneg _),abs_of_nonneg (complex.abs_nonneg _)],
  unfold monoid.pow fact,simp only [complex.abs_div,complex.abs_mul,div_eq_mul_inv,mul_inv',nat.cast_mul,complex.abs_inv],
  have : complex.abs z * complex.abs (monoid.pow z m) * ((complex.abs ↑(fact m))⁻¹ * (complex.abs ↑(succ m))⁻¹) = complex.abs z * complex.abs (monoid.pow z m) * (complex.abs ↑(fact m))⁻¹ * (complex.abs ↑(succ m))⁻¹,ring,rw this,
  have : complex.abs z * (↑n)⁻¹ * (complex.abs (monoid.pow z m) * (complex.abs ↑(fact m))⁻¹) = complex.abs z * complex.abs (monoid.pow z m) * (complex.abs ↑(fact m))⁻¹ * (↑n)⁻¹,ring,
  rw this,
  rw[(by simp : (succ m : ℂ) = ((succ m : ℝ) : ℂ)),complex.abs_of_nonneg],
  refine mul_le_mul_of_nonneg_left _ _,
  rw [inv_le_inv,nat.cast_le],exact le_succ_of_le mn,
  rw [←nat.cast_zero,nat.cast_lt],exact succ_pos _,exact n_pos,rw[←complex.abs_inv,←complex.abs_mul,←complex.abs_mul],
  exact complex.abs_nonneg _,rw[←nat.cast_zero,nat.cast_le],exact zero_le _,
end

lemma complex.exp_series_cau (z : ℂ) : is_cau_seq complex.abs (series (λ m, monoid.pow z m / fact m)) := series_cau_of_abv_cau (complex.exp_series_abs_cau z)

def exp (z : ℂ) : ℂ := complex.lim (series (λ n, monoid.pow z n / fact n))

def sin (z : ℂ) : ℂ := (exp (⟨0, 1⟩ * z) - exp (-⟨0, 1⟩ * z)) / (2 * ⟨0, 1⟩)

def cos (z : ℂ) : ℂ := (exp (⟨0, 1⟩ * z) + exp (-⟨0, 1⟩ * z)) / 2

def tan (z : ℂ) : ℂ := sin z / cos z

def sinh (z : ℂ) : ℂ := (exp z - exp (-z)) / 2

def cosh (z : ℂ) : ℂ := (exp z + exp (-z)) / 2

def tanh (z : ℂ) : ℂ := sinh z / cosh z

@[simp] lemma exp_zero : exp 0 = 1 := begin
  unfold exp,rw [eq_comm,complex.lim_const (complex.exp_series_cau 0)],
  assume ε ε0,existsi 0,assume j j1,
  induction j with j' hi,simpa!,
  replace hi := hi dec_trivial,simp! at *,assumption
end
-- really stupid proof, because there's no of is_cau_seq f * g from is_cau_seq f and is_cau_seq g
lemma exp_add (x y : ℂ) : exp (x + y) = exp x * exp y := begin
 have hxa := complex.exp_series_abs_cau x,
 have hx := complex.exp_series_cau x,
 have hy := complex.exp_series_cau y,
 have hxy := complex.exp_series_cau (x + y),
 unfold exp,rw complex.lim_mul hx hy, 
 have hj : ∀ j : ℕ, series (λ (m : ℕ), monoid.pow (x + y) m / ↑(fact m)) j = series (λ i, series (λ k,monoid.pow x k / fact k * (monoid.pow y (i - k) / fact (i - k))) i) j := sorry,
 have hf := funext hj,simp at hf,have hxy1 := hxy, rw hf at hxy1,
 have := series_cauchy_prod hxa hy,
 rw[eq_comm, complex.lim_eq_lim_iff_equiv (cau_seq.of_near _ ⟨_, hxy⟩ _) hxy],
 assume ε ε0,
 simp [hj],simp at this,
 exact this ε ε0,
 simp [hj], simp at this,exact this,
end
