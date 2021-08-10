theory mi17152_Milos_Milakovic
  imports Main Complex_Main

begin

(* 
link: https://www.imo-official.org/problems/IMO2011SL.pdf
Algebra, zadatak 7
*)

(*
a, b, c pozitivni realni brojevi gde vazi
min(a + b, b + c, c + a) > sqrt(2) i
a^2 + b^2 + c^2 = 3

Dokazati da vazi:

a / (b + c - a)^2 + b / (c + a - b)^2 + c / (a + b - c)^2 \<ge> 3 / (abc)^2
*)

(* Uvodi se funkcija minimuma 2 realna broja *)
fun min :: "real \<Rightarrow> real \<Rightarrow> real" where
"min a b = (if a < b then a else b)"

value "min 5 1"

lemma postavka:
  fixes a b c :: "real"
  assumes "a > 0" "b > 0" "c > 0"
  assumes "min (min (a + b) (b + c)) (c + a) > sqrt 2"
  assumes "a ^ 2 + b ^ 2 + c ^ 2 = 3"
  shows "a / (b + c - a) ^ 2
    + b / (c + a - b) ^ 2
    + c / (a + b - c) ^ 2
    \<ge> 3 / (a * b * c) ^ 2"
  using assms
  oops

find_theorems "sqrt (a^2 + b^2) / sqrt 2 \<ge> (a + b) / 2"
find_theorems "sqrt (a * b) \<le> (a + b) / 2"

lemma nejednakost_aritmeticka_kvadratna_sredina:
  shows "sqrt ((a^2 + b^2) / 2) \<ge> (a + b) / 2"
proof -
  have "(a + b)^2 = a^2 + 2 * a * b + b^2"
    by (simp add: power2_sum)
  then have "(a + b)^2 \<le> 2 * (a^2 + b^2)"
    by (smt (verit, ccfv_threshold) sum_squares_bound)
  then have "a + b \<le> sqrt 2 * sqrt (a^2 + b^2)"
    by (metis real_le_rsqrt real_sqrt_mult)
  then show "sqrt ((a^2 + b^2) / 2) \<ge> (a + b) / 2"
    by (smt (z3) divide_right_mono power2_eq_square real_divide_square_eq real_sqrt_divide real_sqrt_pow2)
qed

(* Narednom lemom se transformise
b + c > sqrt 2 u
b ^ 2 + c ^ 2 > 1 *)
lemma zbir_kvadrata_veci_od_1[simp]:
  fixes b c :: real
  assumes "b > 0" "c > 0"
  assumes "b + c > sqrt 2"
  shows "b ^ 2 + c ^ 2 > 1"
proof -
  have "sqrt ((b^2 + c^2) / 2) \<ge> (b + c) / 2"
    using nejednakost_aritmeticka_kvadratna_sredina by auto
  then have "sqrt ((b^2 + c^2) / 2) > sqrt 2 / 2"
    using assms(3) by fastforce
  then have "sqrt (b^2 + c^2) > sqrt 2 * sqrt 2 / 2"
    by (smt (verit) divide_right_mono nonzero_mult_div_cancel_right real_sqrt_divide real_sqrt_eq_zero_cancel_iff real_sqrt_lt_0_iff times_divide_eq_left)
  then have "sqrt (b^2 + c^2) > 1"
    by simp
  then show "b^2 + c^2 > 1"
    by simp
qed

(* Narednom lemom se dokazuje
a^2 = 3 - (b^2 + c^2) < 2
a < sqrt 2 < b + c

Posto smo prethodnom lemom dokazali da je b^2 + c^2 > 1
ovde cemo uvesti to kao pretpostavku
 *)
lemma a_manje:
  fixes a b c :: real
  assumes "a > 0" "b > 0" "c > 0"
  assumes "b^2 + c^2 > 1"
  assumes "a^2 + b^2 + c^2 = 3"
  shows "a < sqrt  2"
proof -
  have "a^2 = 3 - (b^2 + c^2)"
    using assms(5) by auto
  then show "a < sqrt 2"
    using assms(4) real_less_rsqrt by auto
qed

(* Na osnovu prethodna dva dokaza moze se dokazati
da je b + c - a > 0
Slicno se dokauje i c + a - b > 0 i a + b - c > 0 *)

lemma imenilac:
  fixes a b c :: real
  assumes "a < sqrt 2" "sqrt 2 < b + c"
  shows "b + c - a > 0"
  using assms(1) assms(2) by linarith

lemma holder[simp]:
  fixes x1 x2 x3 y1 y2 y3 :: "real"
  assumes "x1 > 0" "x2 > 0" "x3 > 0" "y1 > 0" "y2 > 0" "y3 > 0"
  shows "x1^3 / y1^2 + x2^3 / y2^2 + x3^3 / y3^2 \<ge> (x1 + x2 + x3) ^ 3 / (y1 + y2 + y3) ^ 2"
  using assms
  sorry

lemma pomoc:
  fixes a b c :: "real"
  assumes "a > 0" "b > 0" "c > 0"
  assumes "a^2 + b^2 + c^2 = 3"
  shows  "((a^2)^3) / (a^5 * (b + c - a)^2) + ((b^2)^3) / (b^5 * (a + c - b)^2)  + ((c^2)^3) / (c^5 * (a + b - c)^2)
    \<ge> (a^2 + b^2 + c^2)^3 / (sqrt (a^5) * (b + c - a) + sqrt (b^5) * (a + c - b) + sqrt (c^5) * (a + b - c))^2"
  using assms
  sorry

lemma primeni_holder_na_levu_stranu:
  fixes a b c :: "real"
  assumes "a > 0" "b > 0" "c > 0"
  assumes "a^2 + b^2 + c^2 = 3"
  shows "a / (b + c - a)^2 + b / (a + c - b)^2 + c / (a + b - c)^2 
     \<ge> 27 / (sqrt (a^5) * (b + c - a) + sqrt (b^5) * (a + c - b) + sqrt (c^5) * (a + b - c))^2"
  using assms
proof -
  have "a / (b + c - a)^2 = ((a^2)) / (a * (b + c - a)^2)"
    by (simp add: power2_eq_square)
  then have lab1: "a / (b + c - a)^2 = ((a^2)^3) / (a^5 * (b + c - a)^2)"
    by (smt (z3) divide_divide_eq_left mult.assoc power2_eq_square power3_eq_cube power4_eq_xxxx power_add_numeral real_divide_square_eq semiring_norm(3))
 have "b / (a + c - b)^2 = ((b^2)) / (b * (a + c - b)^2)"
    by (simp add: power2_eq_square)
  then have lab2: "b / (a + c - b)^2 = ((b^2)^3) / (b^5 * (a + c - b)^2)"
    by (smt (z3) divide_divide_eq_left mult.assoc power2_eq_square power3_eq_cube power4_eq_xxxx power_add_numeral real_divide_square_eq semiring_norm(3))
 have "c / (a + b - c)^2 = ((c^2)) / (c * (a + b - c)^2)"
    by (simp add: power2_eq_square)
  then have lab3: "c / (a + b - c)^2 = ((c^2)^3) / (c^5 * (a + b - c)^2)"
    by (smt (z3) divide_divide_eq_left mult.assoc power2_eq_square power3_eq_cube power4_eq_xxxx power_add_numeral real_divide_square_eq semiring_norm(3))
  from lab1 lab2 lab3 have prem1: "a / (b + c - a)^2 + b / (a + c - b)^2 + c / (a + b - c)^2
    = ((a^2)^3) / (a^5 * (b + c - a)^2) + ((b^2)^3) / (b^5 * (a + c - b)^2)  + ((c^2)^3) / (c^5 * (a + b - c)^2)"
    by simp
  also have prem2: "... \<ge> (a^2 + b^2 + c^2)^3 / (sqrt (a^5) * (b + c - a) + sqrt (b^5) * (a + c - b) + sqrt (c^5) * (a + b - c))^2"
    by (meson assms(1) assms(2) assms(3) assms(4) pomoc)
  have zaklj: "(a^2 + b^2 + c^2)^3 / (sqrt (a^5) * (b + c - a) + sqrt (b^5) * (a + c - b) + sqrt (c^5) * (a + b - c))^2 = 27 / (sqrt (a^5) * (b + c - a) + sqrt (b^5) * (a + c - b) + sqrt (c^5) * (a + b - c))^2"
    by (simp add: assms(4))
  from prem1 prem2 zaklj show  "a / (b + c - a)^2 + b / (a + c - b)^2 + c / (a + b - c)^2 
     \<ge> 27 / (sqrt (a^5) * (b + c - a) + sqrt (b^5) * (a + c - b) + sqrt (c^5) * (a + b - c))^2"
    by linarith
qed

(* Da bi se procenio imenilac sa desne strane nejednakosti
potrebna je schurova nejednakost *)

lemma schur:
  fixes a b c :: real
  assumes "a > 0" "b > 0" "c > 0"
  assumes "a^2 + b^2 + c^2 = 3"
  assumes "a \<ge> b" "b \<ge> c"
  shows "sqrt (a^3) * (a - b) * (a - c)
  + sqrt (b^3) * (b - a) * (b - c)
  + sqrt (c^3) * (c - a) * (c - b) \<ge> 0"
  using assms
proof -
  have u1: "c - a \<le> 0"
    using assms(5) assms(6) by auto
  have u2: "c - b \<le> 0"
    by (simp add: assms(6))
  have u3: "(c - a) * (c - b) \<ge> 0"
    using split_mult_pos_le u1 u2 by blast
  then have "(c - a) * (c - b) * sqrt (c^3)\<ge> 0"
    using assms(3) by force
  then have s2: "sqrt (c^3) * (c - a) * (c - b) \<ge> 0"
    by (metis mult.assoc mult.commute)

  have "sqrt (a^3) * (a - b) * (a - c)
  + sqrt (b^3) * (b - a) * (b - c)
  = sqrt (a^3) * (a - b) * (a - c)
  - (-sqrt (b^3) * (b - a) * (b - c))"
    by simp
  also have "... = sqrt (a^3) * (a - b) * (a - c)
  - sqrt (b^3) * (a - b) * (b - c)"
    by (smt (z3) minus_mult_minus)
  also have "... = (a - b) * (sqrt (a^3) * (a - c) - sqrt (b^3) * (b - c))"
    by (simp add: mult.commute right_diff_distrib')
  finally have isto: "sqrt (a^3) * (a - b) * (a - c)
  + sqrt (b^3) * (b - a) * (b - c) = (a - b) * (sqrt (a^3) * (a - c) - sqrt (b^3) * (b - c))"
    by simp

  have u4: "a - b \<ge> 0"
    by (simp add: assms(5))
  have "a - c \<ge> b - c"
    by (simp add: assms(5))
  then have "sqrt (a^3) * (a - c) \<ge> sqrt (b^3) * (b - c)"
    by (smt (z3) assms(2) mult_le_cancel_left_pos mult_right_less_imp_less power_less_imp_less_base real_sqrt_le_0_iff real_sqrt_le_iff u1 zero_less_power)
  then have "sqrt (a^3) * (a - c) - sqrt (b^3) * (b - c) \<ge> 0"
    by simp
  then have "(sqrt (a^3) * (a - c) - sqrt (b^3) * (b - c)) * (a - b) \<ge> 0"
    by (meson split_mult_pos_le u4)
  then have "(a - b) * (sqrt (a^3) * (a - c) - sqrt (b^3) * (b - c)) \<ge> 0"
    by (simp add: mult.commute)
  then have s1: "sqrt (a^3) * (a - b) * (a - c)
  + sqrt (b^3) * (b - a) * (b - c) \<ge> 0"
    by (simp add: isto)

  then show "sqrt (a^3) * (a - b) * (a - c)
  + sqrt (b^3) * (b - a) * (b - c)
  + sqrt (c^3) * (c - a) * (c - b) \<ge> 0"
    by (simp add: s2)

qed

(* Naredne dve leme se koriste kod leme
imenilac_na_osnovu_schur *)

lemma mnozenje_korena:
  fixes a :: real
  assumes "a > 0"
  shows "sqrt (a^3) * a = sqrt (a^5)"
proof -
  have "sqrt (a^3) * a = sqrt (a^3) * sqrt a * sqrt a"
    using assms by auto
  then have "sqrt (a^3) * a = sqrt (a^3 * a) * sqrt a"
    by (simp add: real_sqrt_mult)
  then have "sqrt (a^3) * a = sqrt (a^4) * sqrt a"
    by (simp add: power3_eq_cube power4_eq_xxxx)
  then have "sqrt (a^3) * a = sqrt (a^4 * a)"
    by (simp add: real_sqrt_mult)
  then show "sqrt (a^3) * a = sqrt (a^5)"
    by (metis numerals(1) power_add_numeral power_one_right semiring_norm(5))
qed

lemma svodjenje_na_trazeni_oblik:
  fixes a b c :: real
  assumes "a > 0" "b > 0" "c > 0"
  shows "sqrt (a^3) * (b * c - a * (b + c - a)) =
  sqrt (a^3) * b * c - sqrt (a^5) * (b + c - a)"
proof -
  have "sqrt (a^3) * (b * c - a * (b + c - a)) =
    sqrt (a^3) * (b * c) - sqrt (a^3) * (a * (b + c - a))"
    by (simp add: right_diff_distrib')
  then have "sqrt (a^3) * (b * c - a * (b + c - a)) =
    sqrt (a^3) * b * c + (-sqrt (a^3) * a * (b + c - a))"
    by simp
  then have "sqrt (a^3) * (b * c - a * (b + c - a)) =
    sqrt (a^3) * b * c - (sqrt (a^3) * a * (b + c - a))"
    by simp
  then show k1: "sqrt (a^3) * (b * c - a * (b + c - a)) =
    sqrt (a^3) * b * c - sqrt (a^5) * (b + c - a)"
    by (simp add: assms(1) mnozenje_korena)
qed

lemma imenilac_na_osnovu_schur:
  fixes a b c :: real
  assumes "a > 0" "b > 0" "c > 0"
  assumes "a^2 + b^2 + c^2 = 3"
  assumes "a \<ge> b" "b \<ge> c"
  shows "sqrt (a^5) * (b + c - a) + sqrt (b^5) * (a + c - b) + sqrt (c^5) * (a + b - c)
    \<le> a * b * c * (sqrt a + sqrt b + sqrt c)"
proof -
  have u1: "sqrt (a^3) * (a - b) * (a - c)
  + sqrt (b^3) * (b - a) * (b - c)
  + sqrt (c^3) * (c - a) * (c - b) \<ge> 0"
    by (simp add: assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) schur)

  have "(a - b) * (a - c) = a * (a - c) - b * (a - c)"
    by (simp add: left_diff_distrib')
  then have u2: "(a - b) * (a - c) = a^2 - a * c - b * a + b * c"
    by (smt (verit) power2_eq_square ring_class.ring_distribs(1))

  have "(b - a) * (b - c) = b * (b - c) - a * (b - c)"
    by (simp add: left_diff_distrib)
  then have u3: "(b - a) * (b - c) = b^2 - b * c - a * b + a * c"
    by (smt (verit) power2_eq_square ring_class.ring_distribs(1))

  have "(c - a) * (c - b) = c * (c - b) - a * (c - b)"
    by (simp add: left_diff_distrib)
  then have u4: "(c - a) * (c - b) = c^2 - c * b - a * c + a * b"
    by (smt (verit) power2_eq_square ring_class.ring_distribs(1))

  from u1 u2 u3 u4 have m: "sqrt (a^3) * (a^2 - a * c - b * a + b * c)
  + sqrt (b^3) * (b^2 - b * c - a * b + a * c)
  + sqrt (c^3) * (c^2 - c * b - a * c + a * b) \<ge> 0"
    by (metis (no_types, hide_lams) ab_semigroup_mult_class.mult_ac(1))

  have m1: "a^2 - a * c - b * a + b * c = b * c - a * (b + c - a)"
    by (smt (verit) mult.commute power2_eq_square ring_class.ring_distribs(1))

  have m2: "b^2 - b * c - a * b + a * c = a * c - b * (a + c - b)"
    by (smt (verit) mult.commute power2_eq_square ring_class.ring_distribs(1))

  have m3: "c^2 - c * b - a * c + a * b = b * a - c * (a + b - c)"
    by (smt (verit) mult.commute power2_eq_square ring_class.ring_distribs(1))


  from m m1 m2 m3 have "sqrt (a^3) * (b * c - a * (b + c - a))
  + sqrt (b^3) * (a * c - b * (a + c - b))
  + sqrt (c^3) * (b * a - c * (a + b - c)) \<ge> 0"
    by auto

  then have "sqrt (a^3) * b * c - sqrt (a^5) * (b + c - a)
  + sqrt (b^3) * a * c - sqrt (b^5) * (a + c - b)
  + sqrt (c^3) * b * a - sqrt (c^5) * (a + b - c) \<ge> 0"
    by (smt (verit) assms(1) assms(2) assms(3) svodjenje_na_trazeni_oblik)

  then have "sqrt (a^5) * (b + c - a) + sqrt (b^5) * (a + c - b) + sqrt (c^5) * (a + b - c)
    \<le> sqrt (a^3) * b * c + sqrt (b^3) * a * c + sqrt (c^3) * b * a"
    by linarith

  then have "sqrt (a^5) * (b + c - a) + sqrt (b^5) * (a + c - b) + sqrt (c^5) * (a + b - c)
    \<le> sqrt a * sqrt a * sqrt a * b * c + sqrt b * sqrt b * sqrt b * a * c + sqrt c * sqrt c * sqrt c * b * a"
    by (metis power3_eq_cube real_sqrt_power)

  then have "sqrt (a^5) * (b + c - a) + sqrt (b^5) * (a + c - b) + sqrt (c^5) * (a + b - c)
    \<le> a * sqrt a * b * c + b * sqrt b * a * c + c * sqrt c * b * a"
    using assms(1) assms(2) assms(3) by fastforce

  then have "sqrt (a^5) * (b + c - a) + sqrt (b^5) * (a + c - b) + sqrt (c^5) * (a + b - c)
    \<le> a * (sqrt a * b * c) + a * (b * sqrt b * c) + a * (c * sqrt c * b)"
    by (simp add: mult.commute mult.left_commute)

  then have "sqrt (a^5) * (b + c - a) + sqrt (b^5) * (a + c - b) + sqrt (c^5) * (a + b - c)
    \<le> a * (sqrt a * b * c + b * sqrt b * c + c * sqrt c * b)"
    by (simp add: distrib_left)

  then have "sqrt (a^5) * (b + c - a) + sqrt (b^5) * (a + c - b) + sqrt (c^5) * (a + b - c)
    \<le> a * (b * (sqrt a * c) + b * (sqrt b * c) + b * (c * sqrt c))"
    by (smt (verit) ab_semigroup_mult_class.mult_ac(1) mult.commute)

  then have "sqrt (a^5) * (b + c - a) + sqrt (b^5) * (a + c - b) + sqrt (c^5) * (a + b - c)
    \<le> a * b * (sqrt a * c + sqrt b * c + c * sqrt c)"
    by (simp add: distrib_left)

  then have "sqrt (a^5) * (b + c - a) + sqrt (b^5) * (a + c - b) + sqrt (c^5) * (a + b - c)
    \<le> a * b * (c * sqrt a + c * sqrt b + c * sqrt c)"
    by (simp add: mult.commute)

  then show "sqrt (a^5) * (b + c - a) + sqrt (b^5) * (a + c - b) + sqrt (c^5) * (a + b - c)
    \<le> a * b * c * (sqrt a + sqrt b + sqrt c)"
    by (simp add: distrib_left)
qed

lemma nejednakost_aritmeticka_i_cetvrti_stepen:
  fixes a b c :: real
  assumes "a > 0" "b > 0" "c > 0"
  assumes "a^2 + b^2 + c^2 = 3"
  shows "((sqrt a + sqrt b + sqrt c) / 3) ^ 4 
    \<le> (a^2 + b^2 + c^2) / 3"
  sorry

lemma manje_od_3:
  fixes a b c :: real
  assumes "a > 0" "b > 0" "c > 0"
  assumes "a^2 + b^2 + c^2 = 3"
  shows "sqrt a + sqrt b + sqrt c \<le> 3"
  using assms
proof -
  from assms have "((sqrt a + sqrt b + sqrt c) / 3) ^ 4 
    \<le> (a^2 + b^2 + c^2) / 3"
    using nejednakost_aritmeticka_i_cetvrti_stepen by blast
  then have "((sqrt a + sqrt b + sqrt c) / 3) ^ 4 
    \<le> 1"
    using assms(4) by auto
  then have "(sqrt a + sqrt b + sqrt c) / 3 \<le> 1"
    by (smt (z3) one_le_numeral power_increasing power_one_right)
  then show "sqrt a + sqrt b + sqrt c \<le> 3"
    by auto
qed

lemma manji_imenilac:
  fixes a b c :: real
  assumes "a > 0" "b > 0" "c > 0"
  assumes "a^2 + b^2 + c^2 = 3"
  assumes "a * b * c * (sqrt a + sqrt b + sqrt c) \<ge> 0"
  assumes "sqrt (a^5) * (b + c - a) + sqrt (b^5) * (a + c - b) + sqrt (c^5) * (a + b - c) \<ge> 0"
  assumes "a \<ge> b" "b \<ge> c"
  shows "(a * b * c * (sqrt a + sqrt b + sqrt c))^2
    \<ge> (sqrt (a^5) * (b + c - a) + sqrt (b^5) * (a + c - b) + sqrt (c^5) * (a + b - c))^2"
  using assms
proof -
  have "sqrt (a^5) * (b + c - a) + sqrt (b^5) * (a + c - b) + sqrt (c^5) * (a + b - c) \<le> a * b * c * (sqrt a + sqrt b + sqrt c)"
    by (simp add: assms(1) assms(2) assms(3) assms(4) assms(7) assms(8) imenilac_na_osnovu_schur)
  then have "(sqrt (a^5) * (b + c - a) + sqrt (b^5) * (a + c - b) + sqrt (c^5) * (a + b - c))^2  \<le> (a * b * c * (sqrt a + sqrt b + sqrt c))^2"
    by (simp add: assms(6) power_mono)
  then show "(a * b * c * (sqrt a + sqrt b + sqrt c))^2
    \<ge> (sqrt (a^5) * (b + c - a) + sqrt (b^5) * (a + c - b) + sqrt (c^5) * (a + b - c))^2"
    by simp
qed

find_theorems name: frac_le

lemma razlomak:
  fixes a b :: real
  assumes "a \<ge> b" "a > 0" "b > 0"
  shows "1 / a \<le> 1 / b"
  using assms
  by (simp add: frac_le)

lemma veci_clan:
  fixes a b c :: real
  assumes "a > 0" "b > 0" "c > 0"
  assumes "a^2 + b^2 + c^2 = 3"
  assumes "a * b * c * (sqrt a + sqrt b + sqrt c) > 0"
  assumes "sqrt (a^5) * (b + c - a) + sqrt (b^5) * (a + c - b) + sqrt (c^5) * (a + b - c) > 0"
  assumes "a \<ge> b" "b \<ge> c"
  shows " 27 / (a * b * c * (sqrt a + sqrt b + sqrt c))^2
    \<le> 27 / (sqrt (a^5) * (b + c - a) + sqrt (b^5) * (a + c - b) + sqrt (c^5) * (a + b - c))^2"
proof -
  have "1 / (a * b * c * (sqrt a + sqrt b + sqrt c))^2
    \<le> 1 / (sqrt (a^5) * (b + c - a) + sqrt (b^5) * (a + c - b) + sqrt (c^5) * (a + b - c))^2"
    using assms(3) assms(4) assms(6) assms(7) assms(8) imenilac_na_osnovu_schur razlomak by force
  then show "27 / (a * b * c * (sqrt a + sqrt b + sqrt c))^2
    \<le> 27 / (sqrt (a^5) * (b + c - a) + sqrt (b^5) * (a + c - b) + sqrt (c^5) * (a + b - c))^2"
    by auto
qed

find_theorems "_ + _ = _ + _"

lemma poslednja_nejednakost:
  fixes a b c :: real
  assumes "a > 0" "b > 0" "c > 0"
  assumes "a^2 + b^2 + c^2 = 3"
  assumes "a * b * c * (sqrt a + sqrt b + sqrt c) \<ge> 0"
  assumes "sqrt a > 0" "sqrt b > 0" "sqrt c > 0"
  assumes "a * b * c * 3 > 0"  
  shows "27 / (a * b * c * (sqrt a + sqrt b + sqrt c))^2
  \<ge> 3 / (a * b * c)^2"
  using assms
proof -
  have "sqrt a + sqrt b + sqrt c \<le> 3"
    by (simp add: assms(1) assms(2) assms(3) assms(4) manje_od_3)
  then have "1 / (sqrt a + sqrt b + sqrt c)
    \<ge> 1 / 3"
    by (smt (z3) assms(2) assms(3) assms(6) frac_le real_sqrt_gt_zero)
  then have "27 / (sqrt a + sqrt b + sqrt c)
  \<ge> 27 / 3"
    by simp
  then have "27 / (a * (sqrt a + sqrt b + sqrt c))
    \<ge> 27 / (a * 3)"
    using assms(1) pos_divide_le_eq by fastforce
  then have "27 * b / (a * (sqrt a + sqrt b + sqrt c))
    \<ge> 27 * b / (a * 3)"
    by (smt (verit, best) assms(1) assms(7) frac_le frac_less2 real_sqrt_ge_0_iff zero_less_divide_iff)
  then have "27 / (a * (sqrt a + sqrt b + sqrt c) * b)
    \<ge> 27 / (a * 3 * b)"
    by (smt (z3) \<open>27 / (a * 3) \<le> 27 / (a * (sqrt a + sqrt b + sqrt c))\<close> assms(1) assms(2) divide_divide_eq_left frac_le zero_less_divide_iff)
  then have "27 / (a * b * (sqrt a + sqrt b + sqrt c))
    \<ge> 27 / (a * b * 3)"
    by (metis (no_types, hide_lams) divide_divide_eq_left divide_divide_eq_right mult_numeral_1)
  then have "27 / (a * b * (sqrt a + sqrt b + sqrt c) * c)
    \<ge> 27 / (a * b * 3 * c)"
    by (smt (verit) assms(3) divide_divide_eq_left divide_eq_0_iff divide_le_cancel divide_le_eq_1 divide_nonneg_neg not_numeral_le_zero numeral_One)
  then have "27 / (a * b * (sqrt a + sqrt b + sqrt c) * c)^2
    \<ge> 27 / (a * b * 3 * c)^2"
    by (smt (z3) assms(1) assms(2) assms(3) frac_less2 nonzero_divide_mult_cancel_right power2_less_eq_zero_iff power_less_imp_less_base zero_less_divide_iff)
  then have "27 / (a * b * (sqrt a + sqrt b + sqrt c) * c)^2
    \<ge> 27 / ((a * b * 3 * c) * (a * b * 3 * c))"
    by (metis numerals(1) power_add_numeral power_one_right semiring_norm(2))
  then have "27 / (a * b * (sqrt a + sqrt b + sqrt c) * c)^2
    \<ge> 27 / (a^2 * b^2 * 3^2 * c^2)"
    by (simp add: power2_eq_square)
  then have "27 / (a * b * (sqrt a + sqrt b + sqrt c) * c)^2
    \<ge> 27 / (a^2 * b^2 * c^2 * 3^2)"
    by simp
  then have "27 / (a * b * (sqrt a + sqrt b + sqrt c) * c)^2
    \<ge> 27 / (a^2 * b^2 * c^2 * (3 * 3))"
    by simp
  then have "27 / (a * b * (sqrt a + sqrt b + sqrt c) * c)^2
    \<ge> 27 / ((a * b * c)^2 * (3 * 3))"
    by (simp add: power_mult_distrib)
  then have "27 / (a * b * (sqrt a + sqrt b + sqrt c) * c)^2
    \<ge> (9 / (3 * 3)) * (3  / ((a * b * c)^2))"
    by linarith
  then have "27 / (a * b * (sqrt a + sqrt b + sqrt c) * c)^2
    \<ge> (9 / 9) * (3  / ((a * b * c)^2))"
    by simp
  then have "27 / (a * b * (sqrt a + sqrt b + sqrt c) * c)^2
    \<ge> 1 * (3  / ((a * b * c)^2))"
    by simp
  then have "27 / (a * b * (sqrt a + sqrt b + sqrt c) * c)^2
    \<ge> 3  / (a * b * c)^2"
    by simp
  then show "27 / (a * b * c * (sqrt a + sqrt b + sqrt c))^2
    \<ge> 3  / (a * b * c)^2"
    by (smt (z3) divide_divide_eq_left divide_divide_eq_left' numerals(1) power_add_numeral power_one_right semiring_norm(2))
qed

lemma zadatak:
  fixes a b c :: "real"
  assumes "a > 0" "b > 0" "c > 0"
  assumes "min (min (a + b) (b + c)) (c + a) > sqrt 2"
  assumes "a ^ 2 + b ^ 2 + c ^ 2 = 3"
  assumes "a * b * c * (sqrt a + sqrt b + sqrt c) > 0"
  assumes "sqrt (a^5) * (b + c - a) + sqrt (b^5) * (a + c - b) + sqrt (c^5) * (a + b - c) > 0"
  assumes "a \<ge> b" "b \<ge> c"
  shows "a / (b + c - a) ^ 2
    + b / (a + c - b) ^ 2
    + c / (a + b - c) ^ 2
    \<ge> 3 / (a * b * c) ^ 2"
proof -
  have "a / (b + c - a)^2 + b / (a + c - b)^2 + c / (a + b - c)^2 
     \<ge> 27 / (sqrt (a^5) * (b + c - a) + sqrt (b^5) * (a + c - b) + sqrt (c^5) * (a + b - c))^2"
    by (meson assms(1) assms(2) assms(3) assms(5) primeni_holder_na_levu_stranu)
  then have "a / (b + c - a)^2 + b / (a + c - b)^2 + c / (a + b - c)^2 
     \<ge> 27 / (a * b * c * (sqrt a + sqrt b + sqrt c))^2"
    using assms(3) assms(5) assms(6) assms(7) assms(8) assms(9) veci_clan by force
  then show "a / (b + c - a)^2 + b / (a + c - b)^2 + c / (a + b - c)^2 
     \<ge> 3 / (a * b * c)^2"
    using assms(1) assms(2) assms(3) assms(5) assms(6) poslednja_nejednakost by fastforce
qed

end