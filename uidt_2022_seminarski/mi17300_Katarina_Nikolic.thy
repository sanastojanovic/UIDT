theory mi17300_Katarina_Nikolic
  imports Complex_Main HOL.Real HOL.Power HOL.Nat HOL.NthRoot
begin 

text‹
Link: https://www.imo-official.org/problems/IMO2016SL.pdf
Algebra A1

Let a, b, and c be positive, real numbers such that min{ab,bc,ca} >= 1. Prove that:
((a^2 + 1)*(b^2 + 1)*(c^2 + 1))^(1/3) ≤ ((a + b + c)/3)^2 + 1
›

declare [[quick_and_dirty = true]]
declare [[show_consts]]

term root
term Min

(*1. DEO - Formulacija zadatka*)

lemma
  fixes a b c :: real
  assumes "a > 0" "b > 0" "c > 0"  "Min {a*b, b*c, c*a} ≥ 1"
  shows "root 3 ((a^2 + 1)*(b^2 + 1)*(c^2 + 1)) ≤ 1 + ((a + b + c)/3)^2"
  sorry

(*2. DEO - Raspisivanje resenja*)


    find_theorems "_ ≤ _ ⟹ root _ _ ≤  root _ _"
    find_theorems "_/_ = 1 "


lemma nejednakost_proizvod:
  fixes x y z t :: real
  assumes "x ≤ y"  "z ≤ t" "x > 0" "y > 0" "z > 0" "t > 0"
  shows "x*z ≤ y*t"
  using assms(1) assms(2) assms(4) assms(5) mult_mono by fastforce

lemma nejednakost_kub:
  fixes x y :: real
  assumes "x > 0" "y > 0"
  shows "x ≤ y ⟹ root 3 x ≤ root 3 y"
  by simp

lemma nejednakost_kvadrati:
  fixes x y :: real
  assumes "x >0 " "y > 0" "x*y ≥ 1"
  shows "(x*y - 1) ≤ (((x+y)/2)^2 - 1)"

proof -
  have "2*x*y ≤ x^2 + y^2"
    by (simp add:sum_squares_bound)
  then have "4*x*y  ≤ x^2 + 2*x*y + y^2"
    by simp
  then have "x*y ≤ (x^2 + 2*x*y + y^2)/4"
    by simp
  then have "x*y ≤ ((x+y)/2)^2"
    by (simp add:power_divide power2_sum)
  then show ?thesis 
    by simp
qed

lemma mnozenje_binoma:
  fixes x y ::real
  shows "(x+1) * (y+1) = x*y + x + y + 1"
proof -
  have "(x+1) * (y+1) = x * (y + 1) + 1 * (y + 1)"
    by (simp add: distrib_right)
  also have "… = x * y + x * 1 + 1 * y + 1 * 1"
    by (simp add: distrib_left)
  finally show ?thesis
    by simp
qed

lemma pomocna_kvadrati: 
  fixes x y :: real
  assumes "x >0 " "y > 0" "x*y ≥ 1"
  shows "(x^2 + 1)*(y^2 + 1) ≤ (1 + ((x+y)/2)^2)^2"
proof -
  have "(x^2 + 1)*(y^2 + 1) =  x^2*y^2 + x^2 + y^2 + 1"
    by (simp add: mnozenje_binoma)
  also have "… =  x^2*y^2 - 2*x*y + 1 + x^2 + 2*x*y + y^2"
    by simp
  also have "… = (x*y-1)^2 + (x+y)^2"
    by (simp add: power2_diff power_mult_distrib power2_sum)
  also have "… ≤ (((x+y)/2)^2 - 1)^2 + (x+y)^2"
    by (simp add:power_mono nejednakost_kvadrati assms)
  also have "… = (((x+y)/2)^2 - 1)^2 + 4*((x+y)/2)^2"
    by (simp add:power_divide)
  also have "… = (((x+y)/2)^2)^2 - 2*((x+y)/2)^2 + 1 +  4*((x+y)/2)^2"
    by (simp add: power2_diff power_mult)
  also have "… = (((x+y)/2)^2)^2 +  2*((x+y)/2)^2 + 1"
    by simp
  also have "… = (1 + ((x+y)/2)^2)^2"
    by (simp add: power2_sum)
  finally show ?thesis
    by simp
qed


lemma pomocna_a:
  fixes a b c :: real 
  assumes "Min {a*b, b*c, a*c} ≥ 1"  "a > 0" "b > 0" "c > 0"
  assumes "a ≥ b" 
  shows "a ≥ 1"
proof - 
   have 0: "a*b ≥ 1" 
    using assms Min_ge_iff
    by simp
  then have "a*a ≥ a*b"
    using assms
    by simp
  then have "a*a ≥ 1"
    using assms 
    using "0"
    by linarith
  then show ?thesis
    by (smt (verit, ccfv_threshold) assms(2) mult_less_cancel_right2)
qed

lemma pomocna_a_kvadrat:
  fixes a :: real
  assumes "a ≥ 1"
  shows "a*a ≥ 1"
  using assms less_1_mult less_eq_real_def by auto

lemma pomocna_ad:
  fixes a b c :: real
  assumes "Min {a*b, b*c, a*c} ≥ 1"  "a > 0" "b > 0" "c > 0" "a ≥ 1"
  shows "a * (a+b+c)/3 ≥ 1"
proof-
  have "a * (a + b+ c)/3 = (a*a + a*b + a*c)/3"
    by (simp add: distrib_left)
  then have "… ≥ (1 + 1 + 1)/3"
  proof-
    have "a*a ≥ 1"
      by (simp add: assms(5) pomocna_a_kvadrat)
    then have "a*a + a*b ≥ 1 + 1"
      using assms Min_ge_iff add_mono
      by auto
    then have "a*a + a*b + a*c ≥ 1 + 1 + 1"
      using assms Min_ge_iff add_mono
      by auto
    then show ?thesis
      by auto
  qed
  then show ?thesis
    using ‹a * (a + b + c) / 3 = (a * a + a * b + a * c) / 3› 
    by auto
qed

lemma glavna:
  fixes a b c ::real
  assumes "Min {a*b, b*c, a*c} ≥ 1"  "a > 0" "b > 0" "c > 0"  "a ≥ b" "b≥ c"
  shows "root 3 ((a^2 + 1)*(b^2 + 1)*(c^2 + 1)) ≤ 1 + ((a + b + c)/3)^2"
proof-
  let "?d" = "(a+b+c)/3" 
  have bc_proizvod: "(b^2 + 1)*(c^2 + 1) ≤ (1 + ((b+c)/2)^2)^2"
  proof-
    have "b*c ≥ 1"
      using assms
      by auto
    then show ?thesis
      using assms pomocna_kvadrati
      by auto
  qed
   have ad_ge_1 :"a*?d ≥ 1"
    proof- 
      have "a ≥ 1"
        using assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) pomocna_a
        by blast
      then show ?thesis
        using assms ‹a ≥ 1› pomocna_ad
        by (metis times_divide_eq_right)
  qed
   have ad_proizvod: "(a^2 + 1)*(?d^2 + 1) ≤ (1 + ((a+?d)/2)^2)^2"
    using ad_ge_1 assms(2) assms(3) assms(4) pomocna_kvadrati
    by force
  then have svi_proizvod: "((a^2+1)*(?d^2+1))*((b^2+1)*(c^2+1)) ≤ (1 + ((a+?d)/2)^2)^2*(1 + ((b+c)/2)^2)^2"
    using assms bc_proizvod mult_mono ad_proizvod 
    by (smt (verit, del_insts) mult_less_0_iff power2_less_eq_zero_iff)
  have korenovi: "((a+?d)/2)*((b+c)/2) ≥ 1"
    proof-
      have "((a+?d)/2)*((b+c)/2) ≥ (sqrt(a*?d))*(sqrt(b*c))"
      proof-
        have 1: "(a+?d)/2 ≥ sqrt(a*?d)"
        by (smt (verit, ccfv_SIG) arith_geo_mean_sqrt assms(4)  assms(5) assms(6) divide_nonneg_nonneg)
      have 2: "(b+c)/2 ≥ sqrt(b*c)"
        using arith_geo_mean_sqrt assms(3) assms(4)
        by auto
      show ?thesis
        using assms(1) assms(2) assms(3) assms(4) "1" "2" mult_mono
        by fastforce
    qed
    then have "(sqrt(a*?d))*(sqrt(b*c)) ≥ 1"
    proof-
      have a : "sqrt(a*?d) ≥ 1"
        using assms pomocna_ad real_sqrt_ge_1_iff
        using ad_ge_1 
        by blast
      have b: "sqrt(b*c) ≥ 1"
        using assms real_sqrt_ge_1_iff Min_ge_iff
        by force
      show ?thesis
        using "a" "b" mult_mono mult_cancel_right2
        by (smt (z3))
    qed
    then show ?thesis
      using ‹sqrt (a * ((a + b + c) / 3)) * sqrt (b * c) ≤ (a + (a + b + c) / 3) / 2 * ((b + c) / 2)› 
      by auto
  qed
  then have adbc_2 :"(((a+?d)/2)^2 + 1) * (((b+c)/2)^2 + 1) ≤ (1 + ((a + ?d + b + c)/4)^2)^2"
  proof-
    have  "(((a+?d)/2)^2 + 1) * (((b+c)/2)^2 + 1) ≤ (1 + ((((a+?d)/2) + ((b+c)/2))/2)^2)^2"
      using assms pomocna_kvadrati korenovi divide_le_0_iff
      by (smt (verit, del_insts))
    then have "… = (1 + (((a+?d)+(b+c))/4)^2)^2"
      using assms add_divide_distrib
      by (metis (mono_tags, opaque_lifting) divide_divide_eq_left num_double numeral_times_numeral)
    then have "… = (1 + ((a+?d+b+c)/4)^2)^2"
      by (simp add: is_num_normalize(1))
    then show ?thesis
      using ‹(((a + (a + b + c) / 3) / 2)⇧2 + 1) * (((b + c) / 2)⇧2 + 1) ≤ (1 + (((a + (a + b + c) / 3) / 2 + (b + c) / 2) / 2)⇧2)⇧2› ‹(1 + (((a + (a + b + c) / 3) / 2 + (b + c) / 2) / 2)⇧2)⇧2 = (1 + ((a + (a + b + c) / 3 + (b + c)) / 4)⇧2)⇧2›
      by linarith
  qed
  then have adbc_4: "(((a+?d)/2)^2 + 1)^2 * (((b+c)/2)^2 + 1)^2 ≤ (1 + ((a + ?d + b + c)/4)^2)^4"
  proof-
    have  "(((a+?d)/2)^2 + 1)^2 * (((b+c)/2)^2 + 1)^2 = ((((a+?d)/2)^2 + 1) * (((b+c)/2)^2 + 1))^2"
      by (simp add: power_mult_distrib)
    then have "… ≤ ((1 + ((a + ?d + b + c)/4)^2)^2)^2"
      using assms adbc_2 divide_le_0_iff nonzero_divide_mult_cancel_left power_mono zero_eq_power2
      by (smt (verit, ccfv_SIG)   )
    then have "… = (1 + ((a + ?d + b + c)/4)^2)^4"
      by auto
    then show ?thesis
      using ‹((((a + (a + b + c) / 3) / 2)⇧2 + 1) * (((b + c) / 2)⇧2 + 1))⇧2 ≤ ((1 + ((a + (a + b + c) / 3 + b + c) / 4)⇧2)⇧2)⇧2› ‹(((a + (a + b + c) / 3) / 2)⇧2 + 1)⇧2 * (((b + c) / 2)⇧2 + 1)⇧2 = ((((a + (a + b + c) / 3) / 2)⇧2 + 1) * (((b + c) / 2)⇧2 + 1))⇧2›
      by presburger
  qed

  then have spojni_1: "((a^2+1)*(?d^2+1))*((b^2+1)*(c^2+1)) ≤ (1 + ((a + ?d + b + c)/4)^2)^4"
    using svi_proizvod adbc_2 adbc_4 
    by (smt (verit, ccfv_SIG))

  then have d_jednakost: "?d = (a + ?d + b + c)/4"
  proof-
    have "(a + ?d + b + c)/4 = (a + ((a+b+c)/3) + b + c)/4"
      by auto
    then have "… = (a/1 + (a+b+c)/3 + b/1 + c/1)/4"
      by auto
    then have "… = (3*a/3 + (a+b+c)/3 + 3*b/3 + 3*c/3)/4"
      using assms nonzero_mult_divide_mult_cancel_left2
      by auto
    then have "… = ((3*a + a + b + c + 3*b + 3*c)/3)/4"
      by auto
    then have "… = ((4*a + 4*b + 4*c)/3)/4"
      by auto
    then have "… = (4*(a+b+c)/3)/4"
      by auto
    then have "… = (a+b+c)/3"
      by auto
    then show ?thesis 
      by auto
  qed

  then have d_kvadrat_jednakost: "(?d^2 + 1)^4 = (1 + ((a + ?d + b + c)/4)^2)^4"
    by (smt (verit, del_insts))
  then have spojni_2:  "((a^2+1)*(?d^2+1))*((b^2+1)*(c^2+1)) ≤ (?d^2 + 1)^4"
    by (simp add: spojni_1)
  then have d_kub: "(a^2+1)*(b^2+1)*(c^2+1) ≤ (?d^2 + 1)^3"
  proof-
    have "(a^2 + 1)*(?d^2+1)*(b^2+1)*(c^2+1) ≤ (?d^2 + 1)^3 * (?d^2 + 1)"
      using spojni_2
      by (simp add: ab_semigroup_mult_class.mult_ac(1) power3_eq_cube power4_eq_xxxx)
    then have "((a^2 + 1)*(?d^2+1)*(b^2+1)*(c^2+1))/(?d^2+1) ≤ ((?d^2 + 1)^3 * (?d^2 + 1))/(?d^2+1) "
      using divide_right_mono assms  divide_eq_0_iff zero_less_power2
      by (smt (verit))
    then have "(a^2+1)*(b^2+1)*(c^2+1)*(?d^2+1)/(?d^2+1) ≤ (?d^2 +1)^3 * (?d^2 + 1)/(?d^2+1)"
      using  ab_semigroup_mult_class.mult.commute
      by simp
    then have "(a^2+1)*(b^2+1)*(c^2+1)*1 ≤ (?d^2+1)^3*1"
    proof-
      have "(?d^2+1)/(?d^2+1) = 1"
        using assms divide_self power2_less_0
        by (smt (verit))
      then show ?thesis 
        by (metis ‹(a⇧2 + 1) * (b⇧2 + 1) * (c⇧2 + 1) * (((a + b + c) / 3)⇧2 + 1) / (((a + b + c) / 3)⇧2 + 1) ≤ (((a + b + c) / 3)⇧2 + 1) ^ 3 * (((a + b + c) / 3)⇧2 + 1) / (((a + b + c) / 3)⇧2 + 1)› times_divide_eq_right)
    qed
    then show ?thesis
      by simp
  qed
  then have "root 3 ((a^2+1)*(b^2+1)*(c^2+1)) ≤ (?d^2 + 1)"
  proof-
    have abc_poz: "(a^2+1)*(b^2+1)*(c^2+1) > 0"
      using assms zero_le_power2 mult_le_0_iff
      by (smt (verit))
    have d_poz: "(?d^2+1) > 0"
      using assms
      by (smt (verit, del_insts) zero_eq_power2 zero_less_power2)
    have d_kub_koren: "(?d^2+1) = root 3 (?d^2+1)^3"
      by auto
    then have "(a^2+1)*(b^2+1)*(c^2+1) ≤ (?d^2+1)^3"
      using d_kub
      by simp
    then have "root 3 ((a^2+1)*(b^2+1)*(c^2+1)) ≤ root 3 ((?d^2+1)^3)" 
      using assms abc_poz d_poz nejednakost_kub d_kub
      by fastforce
    then have "root 3 ((a^2+1)*(b^2+1)*(c^2+1)) ≤ (?d^2+1)"
      using d_kub_koren
      by (simp add: power3_eq_cube real_root_mult)
    then show ?thesis
      by simp
  qed
  then show ?thesis
    by auto
  qed
end


