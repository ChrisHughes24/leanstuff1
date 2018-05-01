import data.int.modeq data.int.basic data.nat.modeq data.equiv data.fintype data.nat.prime data.nat.gcd tactic.norm_num

@[simp] lemma nat.mod_mod (n m : ℕ) : n % m % m = n % m := 
nat.cases_on m (by simp) (λ m, nat.mod_eq_of_lt (nat.mod_lt _ (nat.succ_pos _)))

@[simp] lemma int.mod_mod (a b : ℤ) : a % b % b = a % b :=
or.cases_on (classical.em (b = 0)) (by simp {contextual := tt})
(λ h, int.mod_abs (a % b) b ▸ int.mod_eq_of_lt (int.mod_nonneg _ h) (int.mod_lt _ h))

open int int.modeq
@[reducible]
def Z_aux (n : ℤ) : Type := ℤ

instance Zmod_setoid {n : ℤ} : setoid (Z_aux n) :=
{ r := int.modeq n,
  iseqv := ⟨int.modeq.refl, @int.modeq.symm n, @int.modeq.trans n⟩ }

def Zmod (n : ℤ) : Type := quotient (@Zmod_setoid n)

namespace Zmod

private def add_aux {n : ℤ} (a b : Zmod n) : Zmod n :=
quotient.lift_on₂ a b (λ a b, ⟦a + b⟧) (λ a b c d hac hbd, quotient.sound (modeq_add hac hbd))

private def mul_aux {n : ℤ} (a b : Zmod n) : Zmod n :=
quotient.lift_on₂ a b (λ a b, ⟦a * b⟧) (λ a b c d hac hbd, quotient.sound (modeq_mul hac hbd))

private def neg_aux {n : ℤ} (a : Zmod n) : Zmod n :=
quotient.lift_on a (λ a, ⟦-a⟧) (λ a b hab, quotient.sound (modeq_neg hab))

instance (n : ℤ) : comm_ring (Zmod n) :=
{ add := add_aux,
  add_assoc := λ a b c, quotient.induction_on₃ a b c (λ a b c, quotient.sound (by rw add_assoc)),
  zero := ⟦0⟧,
  zero_add := λ a, quotient.induction_on a (λ a, quotient.sound (by rw zero_add)),
  add_zero := λ a, quotient.induction_on a (λ a, quotient.sound (by rw add_zero)),
  neg := neg_aux,
  add_left_neg := λ a, quotient.induction_on a (λ a, quotient.sound (by rw add_left_neg)),
  add_comm := λ a b, quotient.induction_on₂ a b (λ a b, quotient.sound (by rw add_comm)),
  mul := mul_aux,
  mul_assoc := λ a b c, quotient.induction_on₃ a b c (λ a b c, quotient.sound (by rw mul_assoc)),
  one := ⟦1⟧,
  one_mul := λ a, quotient.induction_on a (λ a, quotient.sound (by rw one_mul)),
  mul_one := λ a, quotient.induction_on a (λ a, quotient.sound (by rw mul_one)),
  left_distrib := λ a b c, quotient.induction_on₃ a b c (λ a b c, quotient.sound (by rw left_distrib)),
  right_distrib := λ a b c, quotient.induction_on₃ a b c (λ a b c, quotient.sound (by rw right_distrib)),
  mul_comm := λ a b, quotient.induction_on₂ a b (λ a b, quotient.sound (by rw mul_comm)) }

instance (n : ℤ) : has_coe ℤ (Zmod n) := ⟨quotient.mk⟩

instance Zmod_coe_nat (n : ℤ) : has_coe ℕ (Zmod n) := ⟨quotient.mk ∘ coe⟩

lemma coe_eq_mk {n : ℤ} : ∀ a : ℤ, (a : Zmod n) = ⟦a⟧ := λ _, rfl

lemma coe_int_add (a b n : ℤ) : ((a + b : ℤ) : Zmod n) = a + b := rfl

lemma coe_int_mul (a b n : ℤ) : ((a * b : ℤ) : Zmod n) = a * b := rfl

lemma coe_int_neg (a n : ℤ) : ((-a : ℤ) : Zmod n) = -a := rfl

lemma coe_int_sub (a b n : ℤ) : ((a - b : ℤ) : Zmod n) = a - b := rfl

lemma coe_nat_add (a b : ℕ) (n : ℤ) : ((a + b : ℕ) : Zmod n) = a + b := rfl

lemma coe_nat_mul (a b : ℕ) (n : ℤ) : ((a * b : ℕ) : Zmod n) = a * b := rfl

lemma coe_nat_sub {a b : ℕ} (n : ℤ) (h : b ≤ a) : ((a - b : ℕ) : Zmod n) = a - b :=
show (((a - b : ℕ) : ℤ) : Zmod n) = a - b, by rw int.coe_nat_sub h; refl

def to_nat {n : ℤ} (a : Zmod n) : ℕ :=
quotient.lift_on a (λ a, to_nat (a % n)) 
  (λ a b (hab : _ = _), or.cases_on (classical.em (n = 0)) 
    (λ hn, by simp * at *)
    (λ hn, int.coe_nat_inj 
      (by simpa [int.to_nat_of_nonneg (mod_nonneg a hn), 
        int.to_nat_of_nonneg (mod_nonneg b hn)])))

lemma to_nat_lt {n : ℤ} (hn : n ≠ 0) (a : Zmod n) : a.to_nat < n.nat_abs :=
quotient.induction_on a (λ a, show (a % n).to_nat < n.nat_abs, 
    from int.coe_nat_lt.1 
      (by rw [int.to_nat_of_nonneg (mod_nonneg a hn), ← abs_eq_nat_abs];
        exact mod_lt _ hn))

def equiv_fin {n : ℤ} (hn : n ≠ 0) : Zmod n ≃ fin (nat_abs n) :=
{ to_fun := λ a, ⟨a.to_nat, to_nat_lt hn a⟩,
  inv_fun := λ a, ⟦a.1⟧,
  left_inv := λ a, quotient.induction_on a (λ a, quotient.sound 
    (show ↑(a % n).to_nat % n = _, 
      by rw to_nat_of_nonneg (mod_nonneg a hn);
        exact int.mod_mod _ _)),
  right_inv := λ ⟨a, ha⟩,
    have ha' : (a : ℤ) < abs n := (abs_eq_nat_abs n).symm ▸ int.coe_nat_lt.2 ha,
    fin.eq_of_veq (show ((a : ℤ) % n).to_nat = a, 
      from int.coe_nat_inj 
        (by rw [to_nat_of_nonneg (mod_nonneg a hn), ← mod_abs];
          exact mod_eq_of_lt (int.coe_nat_le.2 (nat.zero_le a)) ha')) }

def Zmod_fintype {n : ℤ} (hn : n ≠ 0) : fintype (Zmod n) :=
fintype.of_equiv _ (equiv_fin hn).symm

lemma card_Zmod {n : ℤ} (hn : n ≠ 0) : @fintype.card (Zmod n) (Zmod_fintype hn) = n.nat_abs :=
fintype.card_fin n.nat_abs ▸ @fintype.card_congr _ _ (Zmod_fintype hn) _ (equiv_fin hn)

private def inv_aux {n : ℤ} (a : Zmod n) : Zmod n := 
quotient.lift_on a (λ a, (⟦(nat.gcd_a (a.nat_mod n) n.nat_abs : ℤ)⟧ : Zmod n)) 
  (λ a b (hab : _ = _),
     by unfold nat_mod; rw hab)

instance (n : ℤ) : has_inv (Zmod n) := ⟨inv_aux⟩

@[simp] lemma int.gcd_neg (a b : ℤ) : gcd (-a) b = gcd a b :=
by unfold gcd; rw nat_abs_neg

lemma mul_inv_eq_gcd (a n : ℤ) : (a : Zmod n) * a⁻¹ = gcd a n :=
have h : gcd a n = nat.gcd (a.nat_mod n) n.nat_abs := begin
  cases n,
  { unfold int.gcd nat_mod,
    rw [nat.gcd_rec],
    cases classical.em ((n : ℤ).nat_abs = 0),
    simp [h], },
  { unfold nat_mod,
    rw [← neg_of_nat_of_succ, int.gcd, nat.gcd_comm, nat.gcd_def, 
      if_neg],
  }
end,
quotient.sound (begin 
  unfold int.gcd,
  have := nat.gcd_eq_gcd_ab (a.nat_mod n) n.nat_abs,
  rw [nat.gcd_eq_gcd_ab, ← add_zero (a * _)],
  refine modeq_add _ _,

end)

private lemma mul_inv_cancel_aux {p : ℕ} (hp : nat.prime p) {a : Zmod p} : a ≠ 0 →
    a * a⁻¹ = (1 : Zmod p) := 
quotient.induction_on a (λ a (ha : ¬⟦a⟧ = ⟦0⟧),
  have hp0 : (p : ℤ) ≠ 0 := (ne_of_lt (int.coe_nat_lt.2 hp.pos)).symm,
  have h : nat.gcd (nat_mod a p) p = 1 := nat.coprime.gcd_eq_one 
    ((nat.prime.coprime_iff_not_dvd hp).2 
      (λ (h : p ∣ (a % p).to_nat), 
        begin
          rw [← int.coe_nat_dvd, ← modeq_zero_iff, 
            int.to_nat_of_nonneg (mod_nonneg a hp0)] at h,
          have h : a % p = 0 % p := by rw ← int.mod_mod; exact h,
          rw quotient.eq at ha,
          exact ha h,
      end)).symm,
  quotient.sound (begin 
    show _ ≡ ((1 : ℕ) : ℤ) [ZMOD p],
    have bezout := nat.gcd_eq_gcd_ab (nat_mod a p) p,
    rw h at bezout,
    rw [bezout, ← add_zero (a * _), nat_mod, int.to_nat_of_nonneg (mod_nonneg a hp0)],
    exact modeq_add (modeq_mul (int.mod_mod _ _).symm rfl) 
      (modeq.symm (modeq_zero_iff.2 (dvd_mul_right _ _)))
  end))


def Zmod_prime_field {p : ℕ} (hp : nat.prime p) : field (Zmod p) :=
{ inv := has_inv.inv,
  zero_ne_one := λ h, 
    let h : (0 : ℤ) % p = 1 % p := quotient.exact h in
    begin 
      rw mod_eq_of_lt (le_refl (0 : ℤ)) (int.coe_nat_lt.2 hp.pos) at h, 
      rw mod_eq_of_lt (show (0 : ℤ) ≤ 1, by norm_num) (int.coe_nat_lt.2 hp.gt_one) at h,
      exact absurd h dec_trivial,
    end,
  mul_inv_cancel := λ a ha, mul_inv_cancel_aux hp ha,
  inv_mul_cancel := λ a ha, by rw mul_comm; exact mul_inv_cancel_aux hp ha,
  ..Zmod.comm_ring p }

instance (p : {n // nat.prime n}) : field (Zmod p) := Zmod_prime_field p.2


end Zmod
