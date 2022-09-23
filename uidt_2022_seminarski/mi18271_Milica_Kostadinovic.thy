theory Seminarski
  imports Complex_Main
begin

declare [[show_types]]


lemma help0:
  fixes f :: "real \<Rightarrow> real"
  assumes "\<forall>x y. f(f(x) * f(y)) + f(x + y) = f(x*y)"
  shows "f 0 \<le> 0"
  sorry
  
lemma help1:
  fixes f :: "real \<Rightarrow> real"
  fixes x :: real
  assumes "x \<noteq> 1""\<forall>x y. f(f(x) * f(y)) + f(x + y) = f(x*y)"
  shows "f(f(x) * f(x/(x-1))) = 0"
proof-
  have "\<exists> y. y = x/(x-1) \<and> f(f(x) * f(y)) + f(x + y) = f(x*y)"
    using assms(2) by auto
  then obtain y where " y = x/(x-1) \<and> f(f(x) * f(y)) + f(x + y) = f(x*y)" by auto
  then have "f(f(x) * f(x/(x-1))) = 0"
    by (smt (verit, best) assms(1) divide_cancel_left divide_eq_0_iff divide_self left_diff_distrib' nonzero_mult_div_cancel_left nonzero_mult_divide_mult_cancel_left nonzero_mult_divide_mult_cancel_right times_divide_times_eq)
  then show ?thesis by auto
qed


lemma help2:
  fixes f :: "real \<Rightarrow> real"
  fixes x :: real
  assumes "x \<noteq> 1""\<forall>x y. f(f(x) * f(y)) + f(x + y) = f(x*y)"
  shows "f(f(0) * f(0)) = 0"
  by (metis add.commute add_cancel_right_right assms(2) mult_zero_right) 

lemma help3: 
  fixes f :: "real \<Rightarrow> real"
  assumes "f 0 = 0""\<forall>x y. f(f(x) * f(y)) + f(x + y) = f(x*y)"
  shows "\<forall> x. f x = 0"
  by (metis add.commute add.right_neutral assms(1) assms(2) mult_zero_right)


lemma help4: 
  fixes f :: "real \<Rightarrow> real"
  assumes "f 0 < 0""\<forall>x y. f(f(x) * f(y)) + f(x + y) = f(x*y)"
  shows "f 1 = 0"
  by (metis assms(2) help1 help3 mult_eq_0_iff)

lemma help5: 
  fixes f :: "real \<Rightarrow> real"
  assumes "f 0 < 0""\<forall>x y. f(f(x) * f(y)) + f(x + y) = f(x*y)"
  shows "f a = 0 \<longrightarrow> a = 1"
  by (metis assms(1) assms(2) help1 mult_zero_left order_less_irrefl)
  
lemma help6: 
  fixes f :: "real \<Rightarrow> real"
  assumes "f 0 < 0""\<forall>x y. f(f(x) * f(y)) + f(x + y) = f(x*y)"
  shows "(f 0)*(f 0) = 1"
  using assms(1) assms(2) help2 help5 by blast

lemma help7: 
  fixes f :: "real \<Rightarrow> real"
  assumes "f 0 < 0""\<forall>x y. f(f(x) * f(y)) + f(x + y) = f(x*y)"
  shows "f 0  = -1"
proof -
  have "(f 0)*(f 0) = 1" 
    using assms(1) assms(2) help6 by blast
  then have "f 0 = 1 \<or> f 0 = -1" 
    using square_eq_1_iff by blast
  then have "f 0 = -1"
    using assms(1) by fastforce
  then show ?thesis by auto
qed

lemma help8: 
  fixes f :: "real \<Rightarrow> real"
  assumes "f 0 < 0""\<forall>x y. f(f(x) * f(y)) + f(x + y) = f(x*y)"
  shows "f(x + 1)  = f(x) + 1"
  by (metis add.commute add_uminus_conv_diff assms(1) assms(2) diff_add_cancel help4 help7 mult_1 mult_zero_left)

lemma help9:
  fixes f :: "real \<Rightarrow> real"
  fixes n :: int
  assumes "f 0 < 0""\<forall>x y. f(f(x) * f(y)) + f(x + y) = f(x*y)"
  shows "f(x + n)  = f(x) + n"
proof(induction n)
  case (nonneg n)
  then show ?case 
  proof(induction n)
    case 0
    then show ?case by simp
  next
    case (Suc n)
    then show ?case 
      by (smt (verit, ccfv_SIG) assms(1) assms(2) help8 int_ops(4) of_int_1 of_int_add) 
  qed
next
  case (neg n)
  then show ?case 
  proof(induction n)
    case 0
    then show ?case 
      by (smt (verit, best) assms(1) assms(2) help8 int_ops(4) of_int_1 of_int_add of_nat_0)
  next
    case (Suc n)
    then show ?case 
      by (smt (verit, best) assms(1) assms(2) help8 of_int_add of_int_minus of_int_of_nat_eq of_nat_Suc)
  qed
qed

lemma help10:
  fixes f :: "real \<Rightarrow> real"
  fixes n :: int
  assumes "f 0 < 0""\<forall>x y. f(f(x) * f(y)) + f(x + y) = f(x*y)"
  shows "inj f"
  sorry

lemma help11: 
  fixes f :: "real \<Rightarrow> real"
  assumes "f 0 < 0""\<forall>x y. f(f(x) * f(y)) + f(x + y) = f(x*y)"
  shows "\<forall> x. f x = x - 1"
proof
  fix x
  have "\<exists> y. y = - x \<and> f(f(x) * f(y)) + f(x + y) = f(x*y)" 
    by (simp add: assms(2))
  then obtain y where " y = -x \<and> f(f(x) * f(y)) + f(x + y) = f(x*y)" by auto
  then have "f(f(x) * f(y)) + f(x + y) = f(x *(-x))" by auto
  then have "f(f(x) * f(y)) = f(x *(-x) + 1)" 
    by (metis \<open>(y::real) = - (x::real) \<and> (f::real \<Rightarrow> real) (f x * f y) + f (x + y) = f (x * y)\<close> add.commute add.right_inverse add_minus_cancel assms(1) assms(2) help4 mult.commute mult_1 mult_zero_right)
  then have "f(x)*f(y) = x * (-x) + 1" using help10 
    by (meson assms(1) assms(2) injD)
  then have "f(x)*f(-x) = x * (-x) + 1" 
    using \<open>(y::real) = - (x::real) \<and> (f::real \<Rightarrow> real) (f x * f y) + f (x + y) = f (x * y)\<close> by blast
  
  have "\<exists> y1. y1 = 1 - x \<and> f(f(x) * f(y1)) + f(x + y1) = f(x*y1)" 
    by (simp add: assms(2))
  then obtain y1 where " y1 = 1 - x \<and> f(f(x) * f(y1)) + f(x + y1) = f(x*y1)" by auto
  then have "f(f(x)*f(1 - x)) + f(1) = f(x*(1 - x))" by auto
  then have "f(f(x)*f(1 - x)) = f(x*(1 - x))"
    by (simp add: assms(1) assms(2) help4)
  then have "f(x)*f(1 - x) = x*(1 - x)" using help10 
    by (meson assms(1) assms(2) injD)
  then have "f(x)*(1 + f(-x)) = x*(1 - x)" 
    by (metis add.commute assms(1) assms(2) help8 uminus_add_conv_diff)
  then have "f(x) + (x *(-x) + 1) = x*(1 - x)"
    by (simp add: \<open>(f::real \<Rightarrow> real) (x::real) * f (- x) = x * - x + (1::real)\<close> distrib_left) 
  then show "f(x) = x - 1"
    by (simp add: right_diff_distrib')

qed


lemma final1:
  fixes f :: "real \<Rightarrow> real"
  assumes "\<forall>x y. f(f(x) * f(y)) + f(x + y) = f(x*y)"
  shows "(\<forall> x. f x = 0) \<or> (\<forall> x. f x = x - 1) \<or> (\<forall> x. f x = 1 - x)"
  using assms help0 help11 help3 less_eq_real_def by blast



end