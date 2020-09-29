theory mi15158_Zoran_Vujicic_II
  imports Main
begin

text\<open>
 Pravila deljivosti nekih brojeva:
 Kazemo da je broj deljiv brojem 2 ako mu je poslednja cifra parna 
 Kazemo da je broj deljiv brojem 3 ako mu je zbir cifara deljiv brojem 3 
 Kazemo da je broj deljiv brojem 9 ako mu je zbir cifara deljiv brojem 9 
 Kazemo da je broj deljiv brojem 4 ako su mu poslednje dve cifre deljive brojem 4 
 Kazemo da je broj deljiv brojem 8 ako su mu poslednje tri cifre deljive brojem 8 
 Kazemo da je broj deljiv brojem 5 ako mu je poslednja cifra deljiva brojem 5 
 Kazemo da je broj deljiv brojem 6 ako je deljiv brojem 2 i brojem 3 
 Kazemo da je broj deljiv brojem 12 ako je deljiv brojem 3 i brojem 4 
 Kazemo da je broj deljiv brojem 15 ako je deljiv brojem 3 i brojem 5 
 Kazemo da je broj deljiv brojem 18 ako je deljiv brojem 2 i brojem 9 
 Kazemo da je broj deljiv brojem 10 ako mu je poslednja cifra 0 
 Kazemo da je broj deljiv brojem 20 ako su mu poslednje dve cifre deljive brojem 20 
 Kazemo da je broj deljiv brojem 25 ako su mu poslednje dve cifre deljive brojem 25
 Kazemo da je broj deljiv brojem 11 ako mu je razlika izmedju zbira cifara na neparnim 
 mestima i zbira cifara na parnim mestima deljiva brojem 11
\<close>

(* Funkcije koje cemo kasnije koristiti: *)

(* Odvajanje cifara broja i smestanje u listu *)
fun digit_of_num :: "nat \<Rightarrow> nat list" where 
  "digit_of_num n = 
  (if n \<le> 9 
      then [n] 
   else 
      n mod 10 # digit_of_num (n div 10))"

value "digit_of_num 3576"

(* Zbir parnih pozicija *)
fun sum_even_index :: "nat list \<Rightarrow> nat list" where 
  "sum_even_index [x] = []"
| "sum_even_index (x # y # xs) = y # sum_even_index xs"

(* Zbir svih cifara datkog broja *)
abbreviation get_sum :: "nat \<Rightarrow> nat" where
  "get_sum n \<equiv> sum_list (digit_of_num n)"

value "get_sum 365"

(* Zbir neparnih pozicija *)
fun sum_odd_index :: "nat list \<Rightarrow> nat list" where 
  "sum_odd_index [x] = [x]"
| "sum_odd_index (x # y # xs) = x # sum_odd_index xs"

(* Poslednja cifra broja *)
fun first_elem :: "nat list \<Rightarrow> nat" where 
  "first_elem [x] = x" 
| "first_elem (x # xs) = x"

value "first_elem [2,1,6]"

definition last_digit :: "nat \<Rightarrow> nat" where
  "last_digit n = first_elem(digit_of_num n)"

value "last_digit 216"

lemma last_digit_II:
  assumes "n \<ge> 9"
  shows "last_digit n = (n mod 10)"
  using assms
  unfolding last_digit_def
  by simp

(* Poslednje dve cifre broja *)
fun first_two_elem :: "nat list \<Rightarrow> nat" where 
  "first_two_elem [x] = x" 
| "first_two_elem (x # y # xs) = x + y * 10"

value "first_two_elem [4,7,6,9]"

definition last_two_digit :: "nat \<Rightarrow> nat" where
  "last_two_digit n = first_two_elem(digit_of_num n)"

value "last_two_digit 4769"

lemma last_two_digit_II:
  assumes "n \<ge> 9"
  shows "last_two_digit n = (n mod 10) + 10*((n div 10) mod 10)"
  using assms
  unfolding last_two_digit_def
  by simp

(* Poslednje tri cifre broja *)
fun first_three_elem :: "nat list \<Rightarrow> nat" where 
  "first_three_elem [x] = x" 
| "first_three_elem [x, y] = x + y * 10" 
| "first_three_elem (x # y # z # xs) = x + y * 10 + z * 100"

value "first_three_elem [9,8,7,6]"

definition last_three_digit :: "nat \<Rightarrow> nat" where
  "last_three_digit n = first_three_elem(digit_of_num n)"

value "last_three_digit 9876"

lemma last_three_digit_II:
  assumes "n \<ge> 9"
  shows "last_three_digit n = 
        (n mod 10) + 10*((n div 10) mod 10) 
                   + 100*((n div 100) mod 10)"
  using assms
  unfolding last_three_digit_def
  sorry

(* Kazemo da je broj deljiv brojem 3 ako mu je zbir cifara deljiv brojem 3 *)
definition div_III :: "nat \<Rightarrow> bool" where
  "div_III n = 
  (if (get_sum n mod 3 = 0) 
    then True 
   else 
     False)"

value "div_III 27"

declare digit_of_num.simps [simp del]  
lemma get_sum_l:
  shows "get_sum n \<le> n"
proof (induction n rule: digit_of_num.induct)
  case (1 n)
  show ?case
  proof (cases "n \<le> 9")
    case True
    thus ?thesis
      by (simp add: digit_of_num.simps)
  next
    case False
    thus ?thesis
      using 1
      by (simp add: digit_of_num.simps[of n])
  qed
qed

lemma div_III_get_sum:
 shows "3 dvd n \<longleftrightarrow> 3 dvd get_sum n"
 proof-
  have "get_sum n \<le> n"
    by (rule get_sum_l)
  moreover
  have "3 dvd (n - get_sum n)"
  proof (induct n rule: digit_of_num.induct)
    case (1 n)
    show ?case
    proof (cases "n \<le> 9")
      case True
      thus ?thesis
        by (simp add: digit_of_num.simps)
    next
      case False
      have "n = 10*(n div 10) + n mod 10"
        by simp
      hence "n - get_sum n = 10*(n div 10) - get_sum(n div 10)"
        using digit_of_num.simps[of n] `\<not> n \<le> 9`
        by (metis add_diff_cancel_right' diff_diff_left sum_list.Cons)
      hence "n - get_sum n = 9*(n div 10) + (n div 10 - get_sum (n div 10))"
        using get_sum_l[of "n div 10"]
        by auto
      thus ?thesis
        using 1 `\<not> n \<le> 9`
        by simp
    qed
  qed
  ultimately
  show ?thesis
    using dvd_diffD dvd_diffD1
    by blast
qed

(* Kazemo da je broj deljiv brojem 4 ako su mu poslednje dve cifre deljive brojem 4 *)
definition div_IV :: "nat \<Rightarrow> bool" where
  "div_IV n \<equiv> last_two_digit n mod 4 = 0"

value "div_IV 16"

(* Poslednje dve cifre = n mod 100 *)
lemma last_two_remainder: "last_two_digit n = n mod 100"
proof (cases "n < 9")
  case True
  thus ?thesis
    unfolding last_two_digit_def
    by (simp add: digit_of_num.simps)
next
  case False
  thus ?thesis
    using last_two_digit_II[of n]
    unfolding last_two_digit_def
    sorry
qed

(* Relacija izmedju div_IV i last_two_reminder *)
lemma div_IV_exist_m: "div_IV n \<longleftrightarrow> (\<exists>m. n = 4*m)" 
proof
  assume "div_IV n"
  show "\<exists>m. n = 4*m"
  proof-
    from `div_IV n`
    have "(n mod 100) mod 4 = 0"
      unfolding div_IV_def
      using last_two_remainder[of n]
      by auto
    have "n = 100*(n div 100) + n mod 100"
      by auto
    hence "n mod 4 = 0"
      using `(n mod 100) mod 4 = 0`
      by (metis Euclidean_Division.div_eq_0_iff add_diff_cancel_left' add_self_mod_2 
          mod_0_imp_dvd mod_mod_cancel mult_2 mult_mod_right numeral.simps(2) numeral_code(1)
          numerals(2) odd_one odd_two_times_div_two_nat plus_1_eq_Suc rel_simps(51) zero_less_diff)
    thus ?thesis
      by (simp add: mod_eq_0D)
  qed
next
  assume "\<exists>m. n = 4*m"
  show "div_IV n"
  proof-
    from `\<exists>m. n = 4*m`
    have "n mod 4 = 0"
      by auto
    hence "n = 100*(n div 100) + n mod 100"
      unfolding div_IV_def
      by simp
    hence "(n mod 100) mod 4 = 0"
      by (metis \<open>n mod 4 = 0\<close> cong_exp_iff_simps(1) 
          cong_exp_iff_simps(2) dvd_eq_mod_eq_0 mod_mod_cancel)
    thus ?thesis
      by (simp add: div_IV_def last_two_remainder)
  qed
qed

(* Kazemo da je broj deljiv brojem 2 ako mu je poslednja cifra parna *)
definition div_II :: "nat \<Rightarrow> bool" where
  "div_II n \<equiv> last_digit n mod 2 = 0"

lemma last_digit_remainder: "last_digit n = n mod 10"
proof (cases "n < 9")
  case True
  thus ?thesis
    unfolding last_digit_def
    by (simp add: digit_of_num.simps)
next
  case False
  thus ?thesis
    using last_digit_II[of n]
    unfolding last_two_digit_def
    using not_less
    by blast
qed
          
(* Relacija izmedju div_II i last_digit_remainder *)
lemma div_II_exist_m: "div_II n \<longleftrightarrow> (\<exists>m. n = 2*m)" 
proof
  assume "div_II n"
  show "\<exists>m. n = 2*m"
  proof-
    from `div_II n`
    have "(n mod 10) mod 2 = 0"
      unfolding div_IV_def
      using last_digit_remainder[of n]
      by (simp add: div_II_def)
    have "n = 10*(n div 10) + n mod 10"
      by auto
    hence "n mod 2 = 0"
      using `(n mod 10) mod 2 = 0`
      by (metis add_self_mod_2 dvd_eq_mod_eq_0 mod_mod_cancel numeral_Bit0)
    thus ?thesis
      by blast
  qed
next
  assume "\<exists>m. n = 2*m"
  show "div_II n"
  proof-
    from `\<exists>m. n = 2*m`
    have "n mod 2 = 0"
      by auto
    hence "n = 10*(n div 10) + n mod 10"
      unfolding div_II_def
      by simp
    hence "(n mod 10) mod 2 = 0"
      by (metis \<open>n mod 2 = 0\<close> add_self_mod_2 dvd_eq_mod_eq_0 mod_mod_cancel numeral_Bit0)
    thus ?thesis
      by (simp add: div_II_def last_digit_remainder)
  qed
qed

(* Kazemo da je broj deljiv brojem 5 ako mu je poslednja cifra deljiva brojem 5 *)
definition div_V :: "nat \<Rightarrow> bool" where
  "div_V n \<equiv> last_digit n mod 5 = 0"

lemma div_V_exist_m: "div_V n \<longleftrightarrow> (\<exists>m. n = 5*m)" 
proof
  assume "div_V n"
  show "\<exists>m. n = 5*m"
  proof-
    from `div_V n`
    have "(n mod 10) mod 5 = 0"
      unfolding div_V_def
      using last_digit_remainder[of n]
      by (simp add: div_V_def)
    have "n = 10*(n div 10) + n mod 10"
      by auto
    hence "n mod 5 = 0"
      using `(n mod 10) mod 5 = 0`
      by (metis add.right_neutral dvd_eq_mod_eq_0 mod_add_self1 
          mod_mod_cancel mod_mult_self4 mult_div_mod_eq numeral_Bit0)
      thus ?thesis
      by blast
  qed
next
  assume "\<exists>m. n = 5*m"
  show "div_V n"
  proof-
    from `\<exists>m. n = 5*m`
    have "n mod 5 = 0"
      by auto
    hence "n = 10*(n div 10) + n mod 10"
      unfolding div_V_def
      by simp
    hence "(n mod 10) mod 5 = 0"
      by (metis \<open>n mod 5 = 0\<close> dvd_eq_mod_eq_0 mod_mod_cancel 
          mod_mult_self1_is_0 mult_2_right numeral_Bit0)
    thus ?thesis
      by (simp add: div_V_def last_digit_remainder)
  qed
qed

(* Kazemo da je broj deljiv brojem 8 ako su mu poslednje tri cifre deljive brojem 8 *)
definition div_VIII :: "nat \<Rightarrow> bool" where
  "div_VIII n \<equiv> last_three_digit n mod 8 = 0"

value "div_VIII 3320"

(* Poslednje tri cifre = n mod 1000 *)
lemma last_three_remainder: "last_three_digit n = n mod 1000"
proof (cases "n < 9")
  case True
  thus ?thesis
    unfolding last_three_digit_def
    by (simp add: digit_of_num.simps)
next
  case False
  thus ?thesis
    using last_three_digit_II[of n]
    unfolding last_three_digit_def
    sorry
qed

(* Relacija izmedju div_VIII i last_three_remainder *)
lemma div_VIII_exist_m: "div_VIII n \<longleftrightarrow> (\<exists>m. n = 8*m)" 
proof
  assume "div_VIII n"
  show "\<exists>m. n = 8*m"
  proof-
    from `div_VIII n`
    have "(n mod 1000) mod 8 = 0"
      unfolding div_VIII_def
      using last_three_remainder[of n]
      by (simp add: div_VIII_def) 
    have "n = 1000*(n div 1000) + n mod 1000"
      by auto
    hence "n mod 8 = 0"
      using `(n mod 1000) mod 8 = 0`
      by (metis Euclidean_Division.div_eq_0_iff add_diff_cancel_left' add_self_mod_2 
          mod_0_imp_dvd mod_mod_cancel mult_2 mult_mod_right numeral.simps(2) numeral_code(1) 
          numerals(2) odd_one odd_two_times_div_two_nat plus_1_eq_Suc rel_simps(51) zero_less_diff)
      thus ?thesis
        by(simp add: mod_eq_0D)
  qed
next
  assume "\<exists>m. n = 8*m"
  show "div_VIII n"
  proof-
    from `\<exists>m. n = 8*m`
    have " n mod 8 = 0"
      by auto
    hence "n = 1000*(n div 1000) + n mod 1000"
      unfolding div_VIII_def
      by simp
    hence "(n mod 1000) mod 8 = 0" 
      sorry
    thus ?thesis
      by (simp add: div_VIII_def last_three_remainder)
  qed
qed

(* Kazemo da je broj deljiv brojem 9 ako mu je zbir cifara deljiv brojem 9 *)
definition div_IX :: "nat \<Rightarrow> bool" where
  "div_IX n = 
  (if (get_sum n mod 9 = 0) 
    then True 
   else 
     False)"

value "div_IX 3411"

lemma get_sum_l_II:
  shows "get_sum n \<le> n"
proof (induction n rule: digit_of_num.induct)
  case (1 n)
  show ?case
  proof (cases "n \<le> 9")
    case True
    thus ?thesis
      by (simp add: digit_of_num.simps)
  next
    case False
    thus ?thesis
      using 1
      by (simp add: digit_of_num.simps[of n])
  qed
qed

lemma div_IX_get_sum:
 shows "9 dvd n \<longleftrightarrow> 9 dvd get_sum n"
 proof-
  have "get_sum n \<le> n"
    by (rule get_sum_l_II)
  moreover
  have "9 dvd (n - get_sum n)"
  proof (induct n rule: digit_of_num.induct)
    case (1 n)
    show ?case
    proof (cases "n \<le> 9")
      case True
      thus ?thesis
        by (simp add:digit_of_num.simps)
    next
      case False
      have "n = 10*(n div 10) + n mod 10"
        by simp
      hence "n - get_sum n = 10*(n div 10) - get_sum(n div 10)"
        using digit_of_num.simps[of n] `\<not> n \<le> 9`
        by (metis add_diff_cancel_right' diff_diff_left sum_list.Cons)
      hence "n - get_sum n = 9*(n div 10) + (n div 10 - get_sum (n div 10))"
        using get_sum_l[of "n div 10"]
        by auto
      thus ?thesis
        using 1 `\<not> n \<le> 9`
        by simp
    qed
  qed
  ultimately
  show ?thesis
    using dvd_diffD dvd_diffD1
    by blast
qed

(* Kazemo da je broj deljiv brojem 10 ako mu je poslednja cifra 0 *)
definition div_X :: "nat \<Rightarrow> bool" where
  "div_X n \<equiv> last_digit n = 0"

(* Relacija izmedju div_X i last_digit_remainder *)
lemma div_X_exist_m: "div_X n \<longleftrightarrow> (\<exists>m. n = 10*m)" 
proof
  assume "div_X n"
  show "\<exists>m. n = 10 *m"
  proof-
    from `div_X n`
    have "(n mod 10) mod 10 = 0"
      unfolding div_X_def
      using last_digit_remainder[of n]
      by (simp add: div_X_def)
    have "n = 10*(n div 10) + n mod 10"
      by auto
    hence "n mod 10 = 0"
      using `(n mod 10) mod 10 = 0`
      by simp
    thus ?thesis
      by blast
  qed
next
  assume "\<exists>m. n = 10*m"
  show "div_X n"
  proof-
    from `\<exists>m. n = 10*m`
    have "n mod 10 = 0"
      by auto
    hence "n = 10 * (n div 10) + n mod 10"
      unfolding div_X_def
      by auto
    hence "(n mod 10) mod 10 = 0"
      by (simp add: \<open>n mod 10 = 0\<close>)
    thus ?thesis
      by (simp add: div_X_def last_digit_remainder)
  qed
qed

(* Kazemo da je broj deljiv brojem 20 ako su mu poslednje dve cifre deljive brojem 20 *)
definition div_XX :: "nat \<Rightarrow> bool" where
  "div_XX n \<equiv> last_two_digit n mod 20 = 0"

(* Relacija izmedju div_XX i last_two_remainder *)
lemma div_XX_exist_m: "div_XX n \<longleftrightarrow> (\<exists>m. n = 20*m)" 
proof
  assume "div_XX n"
  show "\<exists>m. n = 20*m"
  proof-
    from `div_XX n`
    have "(n mod 100) mod 20 = 0"
      unfolding div_XX_def
      using last_two_remainder[of n]
      by auto
    have "n = 100*(n div 100) + n mod 100"
      by auto
    hence "n mod 20 = 0"
      using `(n mod 100) mod 20 = 0`
      sorry
    thus ?thesis
      by (simp add: mod_eq_0D)
  qed
next
  assume "\<exists>m. n = 20*m"
  show "div_XX n"
  proof-
    from `\<exists>m. n = 20*m`
    have " n mod 20 = 0"
      by auto
    hence "n = 100*(n div 100) + n mod 100 "
      unfolding div_XX_def
      by simp
    hence"(n mod 100) mod 20 = 0"
      sorry
    thus ?thesis
      by (simp add: div_XX_def last_two_remainder)
  qed
qed

(* Kazemo da je broj deljiv brojem 25 ako su mu poslednje dve cifre deljive brojem 25 *)
definition div_XXV :: "nat \<Rightarrow> bool" where
  "div_XXV n \<equiv> last_two_digit n mod 25 = 0"

(* Relacija izmedju div_XXV i last_two_remainder *)
lemma div_XXV_exist_m: "div_XXV n \<longleftrightarrow> (\<exists>m. n = 25*m)" 
proof
  assume "div_XXV n"
  show "\<exists>m. n = 25*m"
  proof-
    from `div_XXV n`
    have "(n mod 100) mod 25 = 0"
      unfolding div_XXV_def
      using last_two_remainder[of n]
      by auto
    have "n = 100*(n div 100) + n mod 100"
      by auto
    hence "n mod 25 = 0"
      using `(n mod 100) mod 25 = 0`
      sorry
    thus ?thesis
      by (simp add: mod_eq_0D)
  qed
next
  assume "\<exists>m. n = 25*m"
  show "div_XXV n"
  proof-
    from `\<exists>m. n = 25*m`
    have " n mod 25 = 0"
      by auto
    hence "n = 100*(n div 100) + n mod 100 "
      unfolding div_XXV_def
      by simp
    hence"(n mod 100) mod 25 = 0"
      by (metis \<open>n mod 25 = 0\<close> mod_0_imp_dvd mod_mod_cancel
          mod_mult_self1_is_0 mod_mult_self4 mult_2_right numeral.simps(2))
    thus ?thesis
      by (simp add: div_XXV_def last_two_remainder)
  qed
qed

(* Kazemo da je broj deljiv brojem 11 ako mu je razlika izmedju zbira cifara na neparnim mestima 
   i zbira cifara na parnim mestima deljiva brojem 11 *)

definition div_XI :: "nat \<Rightarrow> bool" where
  "div_XI n \<equiv> (sum_list(sum_odd_index(digit_of_num n)) 
              -sum_list(sum_odd_index(digit_of_num n))) mod 11 = 0"

lemma div_XI_exist_m: "div_XI n \<longleftrightarrow> (\<exists>m. n = 11*m)" 
proof
  assume "div_XI n"
  show "\<exists>m. n = 11 *m"
    sorry
next
  assume "\<exists>m. n = 11*m"
  show "div_XI n"
    sorry
qed

(* Kazemo da je broj deljiv brojem 6 ako je deljiv brojem 2 i brojem 3 *)
definition div_VI :: "nat \<Rightarrow> bool" where
  "div_VI n \<equiv> div_II n \<and> div_III n"

value "div_VI 30"

(* Kazemo da je broj deljiv brojem 12 ako je deljiv brojem 3 i brojem 4 *)
definition div_XII :: "nat \<Rightarrow> bool" where
  "div_XII n \<equiv> div_III n \<and> div_IV n"

value "div_XII 36"

(* Kazemo da je broj deljiv brojem 15 ako je deljiv brojem 3 i brojem 5 *)
definition div_XV ::"nat \<Rightarrow> bool" where
  "div_XV n \<equiv> div_III n \<and> div_V n"

value "div_XV 225"

(* Kazemo da je broj deljiv brojem 18 ako je deljiv brojem 2 i brojem 9 *)
definition div_XVIII :: "nat \<Rightarrow> bool" where
  "div_XVIII n \<equiv> div_II n \<and> div_IX n"

value "div_XVIII 324"

end