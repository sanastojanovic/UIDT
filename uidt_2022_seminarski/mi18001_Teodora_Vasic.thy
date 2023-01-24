theory mi18001_Teodora_Vasic
  imports Complex_Main 
begin

text\<open>
Link: https://www.imo-official.org/problems/IMO2016SL.pdf
Number Theory N4
Let n, m, k and l be positive integers with n 6= 1 such that n
k +mnl +1 divides n
k+l −1.
Prove that m = 1 and l = 2k or l|k and m = n^(k−l−1)/(n^l-1)
\<close>

declare [[show_types]]
(*Seminarski 1*)
(*lemma final:
  fixes n m k l::nat
  assumes "k > 0""m > 0""l > 0""n > 1""(n^k + m*n^l + 1) dvd (n^(k+l) - 1)"
  shows "(m = 1 \<and> l = 2*k) \<or> ((l dvd k) \<and> m = (n^(k-l) - 1)/(n^l - 1))"
  sorry
*)

lemma help1:
  fixes n m k l::nat
  assumes "k > 0""m > 0""l > 0""n > 1""(n^k + m*n^l + 1) dvd (n^(k+l) - 1)"
  shows "(n^k + m*n^l + 1) dvd (n^(k+l) + n^k + m*n^l)"
proof-
  have "(n^k + m*n^l + 1) dvd (n^(k+l) - 1)" using assms(5) by blast
  then have "(n^k + m*n^l + 1) dvd ((n^(k+l) - 1) + (n^k + m*n^l + 1))" using dvd_add_triv_right_iff by blast
  then have "(n^k + m*n^l + 1) dvd (n^(k+l) + n^k + m*n^l)" by (metis add.commute add_diff_inverse_nat assms(4) group_cancel.add1 not_less_zero power_0 power_strict_increasing_iff)
  then show ?thesis by auto
qed

lemma help2:
  fixes n m k l::nat
  assumes "k > 0""m > 0""l > 0""n > 1""(n^k + m*n^l + 1) dvd (n^(k+l) - 1)""l \<ge> k"
  shows "n^k + m*n^l + 1 dvd n^l + m*n^(l-k) + 1"
proof-
  have "n^l/n^k = n^(l-k)" 
    by (metis One_nat_def Suc_leI assms(4) assms(6) dvd_power_iff_le numerals(2) of_nat_1 of_nat_less_0_iff power_diff real_of_nat_div)
  then have "m*n^l/n^k = m*n^(l-k)" 
    by (metis of_nat_mult times_divide_eq_right)
  then have "n^(k+l)/n^k = n^l" 
    by (metis add_diff_cancel_left' assms(4) le_add1 le_imp_power_dvd not_one_less_zero power_diff real_of_nat_div)
  then have "n^k/n^k = 1" 
    using assms(4) by auto
  then have "(n^(k+l) + n^k + m*n^l)/n^k = (n^l + 1 + m*n^(l-k))" 
    by (metis (no_types, lifting) \<open>real (m * n ^ l) / real (n ^ k) = real (m * n ^ (l - k))\<close> \<open>real (n ^ (k + l)) / real (n ^ k) = real (n ^ l)\<close> add_divide_distrib of_nat_1 of_nat_add)  
  then have "(n^(k+l) + n^k + m*n^l)/n^k = (n^l + m*n^(l-k) + 1)"
    by auto
  have "n^k dvd (n^(k+l) + n^k + m*n^l)" 
    by (simp add: assms(6) le_imp_power_dvd)
  have "(n^k + m*n^l + 1) mod n = 1" 
    using assms(1) assms(4) assms(6) mod_nat_eqI by force
  then have "(n^k + m*n^l + 1) dvd (n^(k+l) + n^k + m*n^l)" using assms(1) assms(2) assms(3) assms(4) assms(5) help1 by presburger
  then have "(n^k + m*n^l + 1) dvd (n^(k+l) + n^k + m*n^l)/n^k" by (metis \<open>(n ^ k + m * n ^ l + 1) mod n = 1\<close> bot_nat_0.not_eq_extremum dvd_def less_numeral_extra(1) mod_0 nonzero_mult_div_cancel_left of_nat_eq_0_iff times_divide_eq_right)
  then have "n^k + m*n^l + 1 dvd n^l + m*n^(l-k) + 1" sorry
  then show ?thesis by fastforce
qed



lemma help3:
  fixes n m k l::nat
  assumes "k > 0""m > 0""l > 0""n > 1""(n^k + m*n^l + 1) dvd (n^(k+l) - 1)""l \<ge> k"
  shows "2*(n^k + m*n^l + 1) > 2*m*n^l + 1"
proof-
  have"2*(n^k + m*n^l + 1) = 2*n^k + 2*m*n^l + 2" by auto
  then have "\<dots> > 2*m*n^l + 1" 
    by linarith
  then show ?thesis by auto
qed

lemma help4:
  fixes n m k l::nat
  assumes "k > 0""m > 0""l > 0""n > 1""(n^k + m*n^l + 1) dvd (n^(k+l) - 1)""l \<ge> k"
  shows "2*m*n^l + 1 > n^l + m*n^(l-k) + 1"
proof-
  have "m*n^l > m*n^(l-k)"
    by (meson assms(1) assms(2) assms(3) assms(4) diff_less mult_less_mono2 power_strict_increasing_iff)
  then have "m*n^l \<ge> n^l" by simp
  then have "2*m*n^l > n^l + m*n^(l-k)" 
    using \<open>(m::nat) * (n::nat) ^ ((l::nat) - (k::nat)) < m * n ^ l\<close> by linarith
  then show ?thesis
    using add_less_mono1 by blast
qed

lemma help5:
  fixes n m k l::nat
  assumes "k > 0""m > 0""l > 0""n > 1""(n^k + m*n^l + 1) dvd (n^(k+l) - 1)""l \<ge> k""2*(n^k + m*n^l + 1) > 2*m*n^l + 1""2*m*n^l + 1 > n^l + m*n^(l-k) + 1"
    "n^k + m*n^l + 1 dvd n^l + m*n^(l-k) + 1"  
  shows "n^k + m*n^l + 1 = n^l + m*n^(l-k) + 1"
proof-
  have "2*(n^k + m*n^l + 1) > n^l + m*n^(l-k) + 1" 
    using assms(7) assms(8) order_less_trans by blast
  then have "n^k + m*n^l + 1 \<ge> n^l + m*n^(l-k) + 1" sorry
  then show ?thesis 
    by (metis add_gr_0 assms(9) le_neq_implies_less less_one nat_dvd_not_less)
qed

  

lemma help6:
   fixes n m k l::nat
  assumes "k > 0""m > 0""l > 0""n > 1""(n^k + m*n^l + 1) dvd (n^(k+l) - 1)""l \<ge> k""2*(n^k + m*n^l + 1) > 2*m*n^l + 1""2*m*n^l + 1 > n^l + m*n^(l-k) + 1"
    "n^k + m*n^l + 1 = n^l + m*n^(l-k) + 1"  
  shows "m = 1 \<and> l = 2*k"
  sorry

lemma help7:
  fixes n m k l::nat
  assumes "k > 0""m > 0""l > 0""n > 1""(n^k + m*n^l + 1) dvd (n^(k+l) - 1)""l < k"
  shows "l dvd k \<and> m = (n^(k-l)-1)/(n^l - 1)"
  sorry

lemma final1:
  fixes n m k l::nat
  assumes "k > 0""m > 0""l > 0""n > 1""(n^k + m*n^l + 1) dvd (n^(k+l) - 1)"
  shows "(m = 1 \<and> l = 2*k) \<or> ((l dvd k) \<and> m = (n^(k-l) - 1)/(n^l - 1))"
  by (metis assms(1) assms(2) assms(3) assms(4) assms(5) help2 help3 help4 help5 help6 help7 linorder_not_less)


end
