theory mi16004_Jelena_Milivojevic

imports Complex_Main 

begin

text \<open>
Link: https://www.imo-official.org/problems/IMO2012SL.pdf
Algebra A3
\<close>

(*  Let a2, \<dots>, an be n − 1 positive real numbers, where n \<ge> 3, such that a2a3 \<sqdot> \<sqdot> \<sqdot> an = 1.
    Prove that: (1+a2)^2*(1+a3)^3...(1+an)^n>n^n *)

find_theorems "_^1"
thm prod.distrib_triv'

lemma weighted_am_gm:
  fixes a :: "real list" and w :: "nat list" and n :: "nat" and B :: "nat"
  assumes "\<forall> i < length a. (a ! i) > 0"
  assumes "\<forall> i < length w. (w ! i) > 0"
  assumes "n = (length a) \<and> n = (length w) \<and> n > 0"
  assumes "B > 0 \<and> (sum_list w)  = B"
  shows "(\<Sum> i = 0..(n-1). (w ! i) * (a ! i)) / B \<ge> root B (\<Prod> i = 0..(n-1). (a ! i) ^ (w ! i))"
  sorry


lemma weighted_am_gm_powered:
  fixes a :: "real list" and w :: "nat list" and n :: "nat" and B :: "nat"
  assumes "\<forall> i < length a. (a ! i) > 0"
  assumes "\<forall> i < length w. (w ! i) > 0"
  assumes "n = (length a) \<and> n = (length w) \<and> n > 0"
  assumes "B > 0" "(sum_list w)  = B"
  shows "((\<Sum> i = 0..(n-1). (w ! i) * (a ! i)) / B) ^ B \<ge> (\<Prod> i = 0..(n-1). (a ! i) ^ (w ! i))"
  using assms
proof -
  have  *:"(\<Sum> i = 0..(n-1). (w ! i) * (a ! i)) / B \<ge> root B (\<Prod> i = 0..(n-1). (a ! i) ^ (w ! i))"  (is "?b \<ge> ?a")
    using assms weighted_am_gm by blast
  show **:"((\<Sum> i = 0..(n-1). (w ! i) * (a ! i)) / B) ^ B \<ge> (\<Prod> i = 0..(n-1). (a ! i) ^ (w ! i))"
  proof -
    have #: "?a > 0"
      by (smt (verit) assms(1) assms(3) assms(4) atLeastAtMost_iff diff_less less_one order_le_less order_less_trans prod_pos real_root_gt_zero zero_less_power)
    also have ##:"?b ^ B \<ge> ?a ^ B"
      using `B > 0` # *  power_mono[of "?a" "?b" "B"] `?a > 0`
      by simp
    finally show ?thesis
      using "#" "##" assms(4) real_root_le_0_iff by force
  qed
qed


lemma am_gm_powered_specialization:
  fixes a1 :: "real" and a2 :: "real" and w1 :: "nat" and w2 :: "nat" and w :: "nat"
  assumes "a1 > 0" "a2 > 0" "w1 > 0" "w2 > 0"
  assumes "w > 0" "w = (w1 + w2)"
  shows "((w1 * a1 + w2 * a2) / w) ^ w \<ge> (a1 ^ w1) * (a2 ^ w2)"
  using assms
proof -
  have #: "length [a1, a2] = length [w1, w2] \<and> length [a1, a2] = 2" 
    by simp
  have ##: "sum_list [w1, w2] = w"
    using `w = w1 + w2`
    by simp
  have *: "\<forall> i < (length [a1, a2]). [a1, a2] ! i > 0" 
    using `a1>0` `a2>0`
    by (simp add: nth_Cons') 
  have **: "\<forall> i < (length [w1, w2]). [w1, w2] ! i > 0" 
    using `w1>0` `w2>0`
    by (simp add: nth_Cons')
  have "(\<Prod>i = 0..1. [a1, a2] ! i ^ [w1, w2] ! i) \<le> ((\<Sum>i = 0..1. ([w1, w2] ! i) * [a1, a2] ! i) /w) ^ w"
    using assms # ## * ** weighted_am_gm_powered[of "a1 # [a2]" "w1 # [w2]" "2" "w"]
    by simp
  then have "([a1, a2] ! 0 ^ [w1, w2] ! 0)*([a1, a2] ! 1 ^ [w1, w2] ! 1) \<le> ((([w1, w2] ! 0) * [a1, a2] ! 0 + ([w1, w2] ! 1) * [a1, a2] ! 1)/w)^w"
    by simp
  then have "(a1 ^ w1)*(a2 ^ w2) \<le> ((w1 * a1 + w2 * a2) / w) ^ w"
    by simp
  then show ?thesis by simp
qed


lemma product_ineq_helper:
  fixes A :: "nat set" and f :: "nat \<Rightarrow> real" and g :: "nat \<Rightarrow> real" and h :: "nat \<Rightarrow> real"
  assumes "(\<Prod> i \<in> A. f i) \<le> (\<Prod> i \<in> A. g i)"
  assumes "(\<Prod> k \<in> A. h k) > 0"
  shows "(\<Prod> k \<in> A. h k) * (\<Prod> i \<in> A. f i) \<le> (\<Prod> k \<in> A. h k) * (\<Prod> i \<in> A. g i)"
  using assms(1) assms(2) by fastforce


lemma prod_helper:
  fixes n :: "nat"
  assumes "n \<ge> 3"
  shows "(\<Prod> i=1..n-1. ((i+1)^(i+1))*((1/(i))^(i))) = n ^ n"
proof (induction n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then show ?case
  proof -
    have "(\<Prod> i=1..n. ((i+1)^(i+1))*((1/(i))^(i))) = (\<Prod> i=1..n-1. ((i+1)^(i+1))*((1/(i))^(i)))*(((1+n)^n+n*(1+n)^n)*(1/ n)^n)"
      using Set_Interval.comm_monoid_mult_class.prod.lessThan_Suc
      by (smt (z3) Nat.add_diff_assoc One_nat_def Suc Suc_leI add.commute add_diff_cancel_left' less_one mult.commute mult_Suc_right of_nat_0_less_iff of_nat_1 of_nat_le_0_iff of_nat_less_0_iff plus_1_eq_Suc power_0 power_add power_one_right prod.cl_ivl_Suc prod_atLeastAtMost_code zero_less_diff)
    also have "\<dots> = (n^n)*(((1+n)^n+n*(1+n)^n)*(1/ n)^n)"
      using Suc
      by simp
    also have "\<dots> = (n^n)*((1+n)*(1+n)^n)*(1/(n^n))"
      by (simp add: power_one_over)
    also have "\<dots> = ((n+1)*(n+1)^n)"
      by auto
    also have "\<dots> = (n+1)^(n+1)"
      by simp
    finally show ?thesis by simp
  qed
qed


lemma final_helper:
  fixes a :: "real list" and n :: "nat"
  assumes "length a = n \<and> n \<ge> 3"
  assumes "(\<Prod> i = 1..(n-1).(a ! i)) = 1"
  assumes "\<forall> k<(length a). (a ! k) > 0"
  shows "(\<Prod> k = 1..(n-1). (k+1)^(k+1))*(\<Prod> i = 1..(n-1). ((((i)*(1/(i)) + 1*(a ! i))/(i+1))^(i+1))) > (\<Prod> k = 1..(n-1). (k+1)^(k+1))*(\<Prod> i = 1..(n-1). (((1/(i))^(i))*((a ! i)^1)))"
  using assms 
proof-
  have $:"(\<Prod> i = 1..(n-1). ((((i)*(1/(i)) + 1*(a ! i))/(i+1))^(i+1))) \<ge> (\<Prod> i = 1..(n-1). (((1/(i))^(i))*((a ! i)^1)))"
  proof -
    have "\<forall>(i::nat). i \<in> {1..n-1} \<longrightarrow> (((1/(i))^(i))*((a ! i)^1)) \<ge> 0 \<and> ((((i)*(1/(i)) + 1*(a ! i))/(i+1))^(i+1)) \<ge> (((1/(i))^(i))*((a ! i)^1))" 
    proof
      fix i :: "nat"
      show "i \<in> {1..n-1} \<longrightarrow> 0 \<le> (1 / real i) ^ i * a ! i ^ 1 \<and> (1 / real i) ^ i * a ! i ^ 1 \<le> ((real i * (1 / real i) + 1 * a ! i) / real (i + 1)) ^ (i + 1)"
      proof 
        assume 1: "i \<in> {1..n-1}"
        have *: "0 < 1/i"
          using 1
          by simp
        then have **: "a ! i > 0" 
          using 1 assms(1) assms(3) 
          by simp
        have ***: "0 < i + 1" 
          using 1 
          by simp
        then have #:"((((i)*(1/(i)) + 1*(a ! i))/(i+1))^(i+1)) \<ge> (((1/(i))^(i))*((a ! i)^1))"
          using * ** *** assms am_gm_powered_specialization[of "1/i" "a ! i" "i" 1 "i+1"]
          by simp
        then have ##: "(((1/(i))^(i))*((a ! i)^1)) \<ge> 0" 
          using 1 `a ! i > 0` 
          by simp
        then show "(((1/(i))^(i))*((a ! i)^1)) \<ge> 0 \<and> ((((i)*(1/(i)) + 1*(a ! i))/(i+1))^(i+1)) \<ge> (((1/(i))^(i))*((a ! i)^1))" 
          using # 
          by simp
      qed 
    qed 
    then have "prod (\<lambda> i. ((((i)*(1/(i)) + 1*(a ! i))/(i+1))^(i+1))) {1..n-1} \<ge> prod (\<lambda> i. (((1/(i))^(i))*((a ! i)^1))) {1..n-1}"
      using Groups_Big.linordered_semidom_class.prod_mono[of "{1..n-1}" "(\<lambda> i. ((1/(i))^(i))*((a ! i)^1))"  "(\<lambda> i. (((i)*(1/(i)) + 1*(a ! i))/(i+1))^(i+1))"]
      by simp
    then show ?thesis by simp 
  qed 
  have $$: "(\<Prod> k = 1..(n-1). (k+1)^(k+1)) > 0" by simp 
  then show ?thesis
    using $ $$ product_ineq_helper[of "(\<lambda> i. ((1/(i))^(i))*((a ! i)^1))" "{1..n-1}" "(\<lambda> i. (((i)*(1/(i)) + 1*(a ! i))/(i+1))^(i+1))" "(\<lambda> k. (k+1)^(k+1))"]
    by (smt (verit, ccfv_threshold) divide_le_eq_1_neg divide_less_0_iff divide_nonpos_pos eq_divide_imp le_divide_eq_1_pos nonzero_mult_divide_mult_cancel_left of_nat_0_less_iff)
qed


(*ak je na poziciji k-1 u nizu a*)
lemma final:
  fixes a :: "real list" and n :: "nat"
  assumes "length a = n \<and> n \<ge> 3"
  assumes "(\<Prod> i = 1..(n-1).(a ! i)) = 1"
  assumes "\<forall> k<(length a). (a ! k) > 0"
  shows "n ^ n < (\<Prod> i = 1..(n-1). (1 + a ! i) ^ (i + 1))"
  using assms 
proof - 
  have "n^n = (n^n)*(\<Prod> i = 1..(n-1).(a ! i)^1)"
    using assms(2)
    by simp 
  also have "\<dots> = (\<Prod> k = 1..(n-1).((k+1)^(k+1))*((1/(k))^(k)))*(\<Prod> i = 1..(n-1).((a ! i)^1))" 
  proof - 
    have "(\<Prod> i=1..n-1. ((i+1)^(i+1))*((1/(i))^(i))) = n^n"
      using  assms(1) prod_helper
      by simp    
    then show "(n^n)*(\<Prod> i = 1..(n-1).(a ! i)^1) = (\<Prod> k = 1..(n-1).((k+1)^(k+1))*((1/(k))^(k)))*(\<Prod> i = 1..(n-1).((a ! i)^1))"
      by simp
  qed 
  also have "\<dots> = (\<Prod> k = 1..(n-1). (k+1)^(k+1))*(\<Prod> j= 1..(n-1).(1/(j))^(j))*(\<Prod> i = 1..(n-1).((a ! i)^1))"
    by (simp add: prod.distrib)
  also have "\<dots> = (\<Prod> k = 1..(n-1). (k+1)^(k+1))*(\<Prod> i = 1..(n-1). (((1/(i))^(i))*((a ! i)^1)))"
    by (simp add: prod.distrib)
  also have "\<dots> <  (\<Prod> k = 1..(n-1). (k+1)^(k+1))*(\<Prod> i = 1..(n-1). ((((i)*(1/(i)) + 1*(a ! i))/(i+1))^(i+1)))"
    using assms final_helper[of "a" "n"]
    by simp 
  also have "\<dots> = (\<Prod> i = 1..(n-1). ((i+1)^(i+1))*((((i)*(1/(i)) + 1*(a ! i))/(i+1))^(i+1)))"
    by (metis of_nat_prod prod.distrib)
  also have "\<dots> = (\<Prod> i = 1..(n-1). ((i+1)^(i+1))*((1/(i+1)*((i)*(1/(i)) + a ! i))^(i+1)))"
    by simp
  also have "\<dots> = (\<Prod> i = 1..(n-1). ((i+1)*(1/(i+1))*((i)*(1/(i)) + a ! i))^(i+1))"
    by (metis (mono_tags, lifting) ab_semigroup_mult_class.mult_ac(1) of_nat_power power_mult_distrib) 
  also have "\<dots> = (\<Prod> i = 1..(n-1). (i*(1/i) + a ! i) ^ (i+1))"
    by simp
  also have "\<dots> = (\<Prod> i = 1..(n-1). (1 + a ! i) ^ (i+1))"
    by simp
  finally show ?thesis .
qed

end
