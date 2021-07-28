theory mi16076_Marija_Markovic

imports Complex_Main HOL.Real

(*
https://www.imo-official.org/problems/IMO2010SL.pdf
A3.
Let x1,..., x100 be nonnegative real numbers such that xi+x(i+1)+x(i+2) \<le> 1 for
all i = 1,..., 100 (we put x101 = x1, x102 = x2). Find the maximal possible 
value of the sum S = \<Sum> i \<in> {1..100}. xi * x(i+2)
*)

begin

lemma square_diff:
  fixes x y :: real
  shows "(x - y)^2 = x^2 - 2*x*y + y^2"
proof -
  have "(x - y)^2 = (x - y) * (x - y)" using power2_eq_square by blast
  also have "... = x * (x - y) - y * (x - y)" using left_diff_distrib by blast
  also have "... = x * x - x * y - y * (x - y)" using right_diff_distrib by auto
  also have "... = x * x - x * y - y * x + y * y" by (simp add: right_diff_distrib)
  also have "... = x^2 - x * y - y * x + y * y" by (simp add: power2_eq_square)
  also have "... = x^2 - x * y - y * x + y^2" by (simp add: power2_eq_square)
  also have "... = x^2 - 2 * x * y  + y^2" by auto
  finally show ?thesis
    .
qed

lemma distrib_rev:
  fixes a b c :: real
  shows "(a * b) + (c * a) = a * (b + c)"
  by (induction a, simp add: ring_class.ring_distribs(1))

lemma square_sum_rev:
  fixes x y :: real
  shows "x^2 + 2*x*y + y^2 = (x + y)^2"
proof -
  have "x^2 + 2 * x * y + y^2 = x^2 +  x * y + x * y + y^2" by auto
  also have "... = x * x +  x * y + x * y + y^2" using power2_eq_square by auto
  also have "... = x * x +  x * y + x * y + y * y" using power2_eq_square by auto
  also have "... = x * (x + y) + x * y + y * y" by (simp add: distrib_left)
  also have "... = x * (x + y) + (x + y) * y" by (simp add: distrib_right)
  also have "... = (x + y) * y + x * (x + y)" by auto
  also have "... = (x + y) * (y + x)" using distrib_rev by auto
  also have "... = (x + y) * (x + y)" by auto
  also have "... = (x + y)^2" by (simp add: power2_eq_square) 
  finally show ?thesis
    .
qed

lemma with_4:
  fixes a b :: real
  shows "4*a*b/4 = a*b"
  apply (induction a) 
  apply auto
  done

lemma ag:
  fixes x y :: real
  shows "x * y \<le> ((x + y) / 2)^2"
 proof -
  have "0 \<le> (x - y)^2" by auto
  also have "... = x^2 - 2*x*y + y^2" using square_diff by auto
  also have "... = x^2 + 2*x*y + y^2 - 4*x*y" by auto
  also have "... = (x + y)^2 - 4*x*y"using square_sum_rev by auto
  also have "4*x*y \<le> (x + y)^2" using calculation by auto
  also have "(4*x*y)/4 \<le> (x + y)^2 / 4" using \<open>4 * x * y \<le> (x + y)\<^sup>2\<close> by auto
  then have "x*y \<le> (x + y)^2 / 4" using with_4 by auto
  then have "... = (x + y)^2 / (2^2)" by auto
  then have "... = ((x + y) / 2)^2" by (metis power_divide)
  then show ?thesis
  using \<open>(x + y)\<^sup>2 / 4 = (x + y)\<^sup>2 / 2\<^sup>2\<close> \<open>x * y \<le> (x + y)\<^sup>2 / 4\<close> by presburger
qed

lemma sum_const:
  fixes a b :: nat
  fixes c :: real
  assumes "a \<le> b"
  shows "(\<Sum> i = a..b. c) = (b - a + 1) * c"
  using assms card_atLeastAtMost[of a b]
  by auto

lemma zero:
  shows "0 * 0 \<le> 1/4"
proof -
  have "0 * 0 = 0" sorry
  also have "... \<le> 1/4" sorry
  finally show ?thesis
    .
qed

lemma four:
  shows "(1/2) * (1/2) \<le> 1/4"
proof -
  have "(1/2) * (1/2) = 1/4" sorry
  also have "... \<le> 1/4" sorry
  finally show ?thesis
    .
qed

lemma sabirak:
  fixes i :: nat
    assumes "1 \<le> i" "i \<le>100" "x = (\<lambda> i. if even i then 0 else 1/2)"
    shows "x i * x (i + 2) \<le> 1/4" 
  using assms
  apply auto
   apply (rule zero)
  apply (rule four)
  done

lemma deo_1:
  fixes x :: "nat \<Rightarrow> real"
  assumes "x = (\<lambda> i. if even i then 0 else 1/2)"
  shows "x 101 = x 1" "x 102 = x 2"
        "\<forall> i. 1 \<le> i \<and> i \<le> 100 \<longrightarrow> x i + x (i + 1) + x (i + 2) \<le> 1"
  using assms
    apply auto
  done

lemma to_sum:
  fixes i n ::nat
  fixes a b :: real
  shows "n * a*b = (\<Sum> i = 1..n. a*b)"
  by auto

(* koliko ima neparnih od 1 do 100*)
(*
lemma even_sum:
  fixes i :: nat
  fixes x :: "nat \<Rightarrow> real"
  assumes "even i" "x i = 0" "x (i + 2) = 0"
  shows "(\<Sum> i = 1..100. x i * x (i + 2)) = 50 * 0"
  using assms
  apply auto
proof -
  have "\<forall> i. even i \<longrightarrow> ((\<Sum>i = 1..100. x i * x (i + 2)) = (\<Sum>i = 1..50. 0 * 0))" using assms by  
qed
*)

lemma deo_2:
  fixes x :: "nat \<Rightarrow> real"
  assumes "x = (\<lambda> i. if even i then 0 else 1/2)"
  shows "(\<Sum> i = 1..100. x i * x (i + 2)) = 25 / 2"
 proof -           (*\<Sum> i = 1..100. x i * x (i + 2)) = 50 * 0 + 50 * (1/2)^2*)
   have "(\<Sum> i = 1..100. x i * x (i + 2)) = (50 * (1/2)*(1/2))" using assms sorry 
   also have "...= (\<Sum> i = 1::nat..50. ((1::real)/2)*((1::real)/2))" using to_sum by auto
   also have "... =  (\<Sum> i = 1::nat..50. ((1::real)/2)^2)" by (simp add: power2_eq_square)
   also have "... =  (\<Sum> i = 1::nat..50. ((1::real)/4))" by (simp add: power_divide)
   also have "... = (50::real) / 4" using sum_const by simp
   also have "... = (25::real) / 2" by simp
   finally show ?thesis
     .
 qed

lemma nejed1:
  fixes x :: "nat \<Rightarrow> real"
  assumes "x = (\<lambda> i. if even i then 0 else 1/2)"  "1 \<le> i" "i \<le> 50"
  shows "x (2*i - 1) \<le> 1 - x 2*i - x (2*i + 1)" 
  using assms by auto 

lemma nejed2:
  fixes x :: "nat \<Rightarrow> real"
  assumes "x = (\<lambda> i. if even i then 0 else 1/2)"  "1 \<le> i" "i \<le> 50"
  shows "x (2*i + 2) \<le> 1 - x 2*i - x (2*i + 1)" 
  using assms by auto 

lemma pomocna:
  fixes x :: "nat \<Rightarrow> real"
  assumes "x = (\<lambda> i. if even i then 0 else 1/2)"  "1 \<le> i" "i \<le> 50"
  shows "x (2*i - 1) * x (2*i + 1) + x (2*i) * x (2*i + 2) \<le>
              (x (2*i) + x (2*i + 1)) * (1 - x (2*i) - x (2*i + 1))"
proof -
  have "x (2*i - 1) * x (2*i + 1) + x (2*i) * x (2*i + 2) \<le> (1 - x (2*i) - x (2*i + 1)) * (x (2*i + 1)) + (x (2*i)) * (1 - x (2*i) - x (2*i + 1))" using nejed1 nejed2 assms by auto
  also have "... = (x (2*i) + x (2*i + 1)) * (1 - x (2*i) - x (2*i + 1))" using distrib_rev by auto 
  finally show ?thesis
      .
  qed

lemma less_sum:
  fixes a b :: nat
  fixes x y :: real
  assumes "x \<le> y"
  shows "(\<Sum> i = a..b. x) \<le> (\<Sum> i = a..b. y)"
  using assms
  by (meson sum_mono)

lemma
  fixes x :: "nat \<Rightarrow> real"
  assumes "x 101 = x 1" "x 102 = x 2"
  assumes "\<forall> i. 1 \<le> i \<and> i \<le> 100 \<longrightarrow> x i + x (i + 1) + x (i + 2) \<le> 1"
  shows "(\<Sum> i = 1..100. x i * x (i + 2)) \<le> 25 / 2"
proof-
  have *: "\<forall> i. 1 \<le> i \<and> i \<le> 50 \<longrightarrow>
           x (2*i - 1) * x (2*i + 1) + x (2*i) * x (2*i + 2) \<le> 1 / 4"
  proof safe
 fix i :: nat
    assume "1 \<le> i" "i \<le> 50"
    then have "x (2*i - 1) * x (2*i + 1) + x (2*i) * x (2*i + 2) \<le>
              (x (2*i) + x (2*i + 1)) * (1 - x (2*i) - x (2*i + 1))"
      using pomocna assms by blast
    also have "... \<le> (((x (2*i) + x (2*i + 1)) + (1 - x (2*i) - x (2*i + 1))) / 2)^2"
      by (rule ag) 
    also have "... = 1/4"
      by (auto simp add: power2_eq_square)
    finally show "x (2*i - 1) * x (2*i + 1) + x (2*i) * x (2*i + 2) \<le> 1 / 4"
      .
  qed

  have "(\<Sum> i = 1..100. x i * x (i + 2)) =
        (\<Sum> i = 1..50. x (2*i - 1) * x (2*i + 1) + x (2*i) * x (2*i + 2))"
  (*proof -
    have "\<forall> i. 1 \<le> i \<and> i \<le> 50 \<longrightarrow> x (2*i - 1) \<le> 1 - x (2*i) - x (2*i + 1)" using assms by auto
    have "\<forall> i. 1 \<le> i \<and> i \<le> 50 \<longrightarrow> x (2*i + 2) \<le> 1 - x (2*i) - x (2*i + 1)" using assms by auto
    have "\<forall> i. 1 \<le> i \<and> i \<le> 50 \<longrightarrow> 
(x (2*i-1)) * (x (2*i+1)) + (x 2*i) * (x (2*i+2)) \<le> (1 - x 2*i - x (2*i + 1)) * (x (2*i+1))
  qed*)
    sorry
  moreover have "(\<Sum> i = 1..50. x (2*i - 1) * x (2*i + 1) + x (2*i) * x (2*i+ 2)) \<le> 50 * (1 / 4)"
    using *
  proof -
    have "(\<Sum> i = 1..50. (x (2*i - 1) * x (2*i + 1) + x (2*i) * x (2*i+ 2))) \<le> (\<Sum> i = 1::nat..50. (1::real)/4)" using [[show_types]] * to_sum less_sum sorry
    also have "... = (50::real) / 4" using sum_const by simp
    also have "...  = (50::real) * (1/4)" by auto
    finally show ?thesis
      .
  qed
 
  ultimately
  show ?thesis
    by auto
qed

find_theorems "(\<Sum>_ \<in> _. _) = (\<Sum>_ \<in> _. _)"
thm Groups_Big.comm_monoid_add_class.sum.inter_filter

end
