theory mi18024_Pavle_Cvejovic
  imports Complex_Main

begin

declare [[show_types]]
declare [[show_sorts]]
declare [[show_consts]]

text\<open>
Link: https://www.imo-official.org/problems/IMO2013SL.pdf

Number Theory: N1

Zadatak: Pronadji sve funkcije f koje slikaju pozitivne cele brojeve (prirodni brojevi bez 0) u pozitivne cele brojeve 
takve da  m^2 + f(n) | mf(m) + n za sve pozitivne cele brojeve m i n

Resenje: f(n) = n
\<close>

(* 1. DEO - Formulacija zadatka  *)

lemma
  fixes f :: "nat \<Rightarrow> nat"
  assumes "\<forall>x>0. f x \<noteq> 0"
  assumes "\<forall>m>0.\<forall>n>0. m^2 + f n dvd m * f m + n"
  shows "\<forall>n>0. f n = n"
  sorry


(*2. DEO - Raspisivanje dokaza prvog dela seminarskog  *)

(* ako je a \<le> b i ako 2*a > b  i ako a deli b onda su oni jednaki
 (moraju uslovi i a deli b i a \<le> b, jer je 0 maskimalni broj u odnosu na relaciju deljivosti u skupu N) 
*)
lemma least_twice_larger_divides_equal:
  fixes a b :: nat
  assumes "a \<le> b \<and> 2*a > b \<and> a dvd b"
  shows "a = b"
  using assms
  by (metis One_nat_def add_0_left div_nat_eqI dvdE mult.commute mult.right_neutral mult_zero_right nonzero_mult_div_cancel_left one_add_one plus_nat.simps(2))

(* ako su m = n = 2 onda je f(2) = 2 *)
lemma f_2_eq_2:
  fixes m n :: nat
  fixes f :: "nat \<Rightarrow> nat"
  assumes "m = 2"
  assumes "n = 2"               
  assumes "\<forall>x>0. f x \<noteq> 0"
  assumes "m^2 + f n dvd m * f m + n"
  shows "f 2 = 2"
  using assms
proof-
  have start_step: "4 + f 2 dvd 2 * f 2 + 2" 
    using assms 
    by auto
  then have "2 * f 2 + 2 < 2 * (4 + f 2)" 
    using assms 
    by auto
  then have "2 * f 2 + 2 = 4 + f 2" 
    using assms least_twice_larger_divides_equal
    by (metis start_step add_gr_0 dvd_imp_le pos2)
  then show ?thesis
    by auto
qed

(* ako su a i b veci od 0 i a deli b onda je i a \<le> b *)
lemma dvd_less:
  fixes a b :: nat
  assumes "a > 0"
  assumes "b > 0"
  assumes "a dvd b"
  shows "a \<le> b"
  using assms
  by auto

(* show f(n) \<le> n *)
lemma final_le:
  fixes m n :: nat
  fixes f :: "nat \<Rightarrow> nat"
  assumes "m = 2"
  assumes "n > 0"
  assumes "\<forall>x>0. f x \<noteq> 0"
  assumes "\<forall>m>0.\<forall>n>0. m^2 + f n dvd m * f m + n"
  shows "f n \<le> n"
proof-
  have "f m = 2" 
    using assms f_2_eq_2
    by (metis add_pos_nonneg nle_le not_one_le_zero one_add_one zero_less_one)
  also have "4 + f n dvd 4 + n" 
    using assms f_2_eq_2
    by (metis mult_2_right numeral_Bit0 pos2 power2_eq_square)
  then have "4 + f n \<le> 4 + n" 
    using dvd_imp_le numeral_eq_Suc 
    by auto
  then show "f n \<le> n" by auto
qed

(* show f(n) \<ge> n *)
lemma final_ge:
  fixes m n :: nat
  fixes f :: "nat \<Rightarrow> nat"
  assumes "m > 0"
  assumes "n > 0"
  assumes "m = n"
  assumes "\<forall>x>0. f x \<noteq> 0"
  assumes "m^2 + f n dvd m * f m + n"
  shows "f n \<ge> n"
proof-
  have "n^2 + f n dvd n * f n + n" 
    using assms
    by blast
  also have "n^2 + f n \<le> n * f n + n" 
    using assms
    by (simp add: dvd_imp_le)
  then have "n^2 - n + f n - f n * n \<le> 0" 
    using assms 
    by (simp add: mult.commute power2_eq_square)
  then have "n * (n - 1) + f n - f n * n \<le> 0" 
    using assms
    by (simp add: power2_eq_square right_diff_distrib')
  then have "n * (n - 1) - f n * (n - 1) \<le> 0" 
    using assms
    by (metis Nat.diff_diff_right bot_nat_0.extremum_unique le_diff_conv le_eq_less_or_eq mult.right_neutral not_less right_diff_distrib' zero_less_diff)
  then have "(n - f n) * (n - 1) \<le> 0" 
    using assms diff_mult_distrib 
    by presburger   
  then have "n - f n \<le> 0"
    using assms
    by (metis One_nat_def Suc_pred bot_nat_0.extremum_uniqueI bot_nat_0.not_eq_extremum diff_is_0_eq' dvd_imp_le dvd_triv_left mult.commute mult.right_neutral mult_is_0)
  then have "n \<le> f n" 
    by auto
  then show ?thesis 
    .
qed


lemma final:
  fixes f :: "nat \<Rightarrow> nat"
  assumes "\<forall>x>0. f x \<noteq> 0"
  assumes "\<forall>m>0.\<forall>n>0. m^2 + f n dvd m * f m + n"
  shows "\<forall>n>0. f n = n"
  using assms 
proof-
  have m_eq_2: "\<exists>m1.\<forall>n1>0. m1=2 \<and> m1^2 + f n1 dvd m1 * f m1 + n1" 
    using assms
    by (metis power_eq_0_iff power_zero_numeral)
  then obtain m1 where " (m1 = 2) \<and> (\<forall>n1>0. m1^2 + f n1 dvd m1 * f m1 + n1)"  
    using assms
    by metis
  then have "m1=2" 
    by auto

  then have n_all: "\<exists>n1>0.\<forall>m1>0. n1 > 0 \<and> m1^2 + f n1 dvd m1 * f m1 + n1" 
    using assms
    by (metis power_eq_0_iff power_zero_numeral)
  then obtain n1 where "(n1 > 0) \<and> (\<forall>m1>0. m1^2 + f n1 dvd m1 * f m1 + n1)"  
    using assms
    by metis
  then have n1_ge_0: "n1 > 0" 
    by auto

  then have f_le: "f n1 \<le> n1" 
    using assms final_le \<open>m1 = 2\<close>
    by presburger

  then have mn_eq: "\<exists>m2>0. m2=n1 \<and> m2^2 + f n1 dvd m2 * f m2 + n1" 
    using assms n1_ge_0
    by presburger
  then obtain m2 where  "(m2 = n1) \<and> (\<forall>n1>0. m2^2 + f n1 dvd m2 * f m2 + n1)"  
    using assms n1_ge_0
    by presburger
  then have "m2 = n1" 
    by auto 

  then have "f n1 \<ge> n1"
    using assms mn_eq final_ge
    by presburger

  then have "f n1 = n1" 
    using assms f_le
    by linarith

  then show ?thesis 
    using assms
    by (metis final_le final_ge nle_le)
qed

end