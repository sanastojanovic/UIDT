theory mi17169_Pavle_Savic
  imports HOL.Real Complex_Main 
begin

text \<open>

Link ka zadatku: https://www.imo-official.org/problems/IMO2009SL.pdf  Algebra A2

Formulacija zadatka: Neka su a, b, c pozitivni realni brojevi takvi da 1/a + 1/b + 1/c = a + b + c. 
Dokazati da vazi: 1 / (2*a + b + c)^2 + 1 / (2*b + c + a)^2 + 1 / (2*c + a + b)^2 \<le> 3/16.

\<close>

declare [[quick_and_dirty = true]]
term sqrt
term root

find_theorems "sqrt _ * _"
find_theorems "_ * (_ / _)"

thm arith_geo_mean
thm arith_geo_mean_sqrt
thm add_pos_pos
thm divide_pos_pos
thm mult_pos_pos
thm times_divide_eq_right

lemma AM_GM_nejednakost:
  fixes x y z :: real
  assumes "x > 0" "y > 0" "z > 0"
  shows "2*x + y + z \<ge> 2 * sqrt((x+y) * (x+z))"
proof -
  have *:"sqrt((x+y) * (x+z)) \<le> ((x+y) + (x+z)) / 2"
    using assms arith_geo_mean_sqrt add_pos_pos
    by (smt (verit))

  have "2 * sqrt((x+y) * (x+z)) \<le> (x+y) + (x+z)"
    using * by auto
  also have "... = 2 * x + y +z"
    by auto
  finally show ?thesis
    .
qed
    
thm frac_le

lemma pomocna_kolicnik:
  fixes x y :: real
  assumes "x > 0" "y > 0"
  assumes "x \<ge> y"
  shows "1 / x^2 \<le> 1 / y^2"
  using assms
  by (simp add: frac_le)

lemma pomocna_kolicnik_2:
  fixes x y a :: real
  assumes "x > 0" "y > 0" "a > 0"
  assumes "x \<ge> y"
  shows "a / x \<le> a / y"
  using assms
  by (simp add: frac_le)

lemma pomocna_kolicnik_3:
  fixes x y a :: real
  assumes "a > 0"
  assumes "x \<ge> y"
  shows "x / a \<ge> y / a"
  using assms
  by (simp add: divide_le_cancel)

lemma manje_proizvod:
  fixes x y a :: real
  assumes "a > 0"
  assumes "x \<ge> y"
  shows "a * x \<ge> a * y"
  using assms
  by auto

lemma koren_kvadrat_jednakost:
  fixes x :: real
  assumes "x > 0"
  shows "(sqrt x)^2 = x"
  using assms
  by simp
  
lemma pomocna_lema:
  fixes x y z :: real
  assumes "x > 0" "y > 0" "z > 0"
  shows "1 / (2*x + y + z)^2 \<le> 1 / (4 * (x+y) * (x+z))"
proof -
  have "1 / (2*x + y + z) ^ 2 \<le> 1 / (2 * sqrt((x+y) * (x+z)))^2"
    using assms AM_GM_nejednakost[of x y z] pomocna_kolicnik[of "2 * x + y + z" "2 * sqrt((x+y) * (x+z))"] 
    by simp
  also have "... =  1 / (4 * sqrt((x+y) * (x+z))^2)"
    by auto
  also have "... = 1 / (4 * sqrt(x+y)^2 * sqrt(x+z)^2)"
    by (simp add: power_mult_distrib real_sqrt_mult)
  also have "... = 1 / (4 * (x+y) * (x+z))"
    using assms koren_kvadrat_jednakost
    by auto
  finally show ?thesis .
qed

thm real_sqrt_mult
thm real_sqrt_power

lemma AM_GM_nejednakost_2:
  fixes x y z :: real
  assumes "x > 0" "y > 0" "z > 0"
  shows "x^2 * y^2 + x^2 * z^2 \<ge> 2 * x^2 * y * z"
proof -

  have *: "sqrt((x^2 * y^2) * (x^2 * z^2)) \<le> ((x^2 * y^2) + (x^2 * z^2)) / 2"
    using assms arith_geo_mean_sqrt
    by auto

  have "2 * x^2 * y * z = 2 * sqrt(x^4) * sqrt(y^2) * sqrt(z^2)"
    using assms koren_kvadrat_jednakost
    by (metis num_double power_mult_numeral real_sqrt_power)
  also have "... = 2 * sqrt (x^4 * y^2 * z^2)"
    by (simp add: real_sqrt_mult)
  also have "... = 2 * sqrt ((x^2 * y^2) * (x^2 * z^2))"
    by simp
  also have "... \<le> (x^2 * y^2) + (x^2 * z^2)"
    using * by auto
  finally show ?thesis .
qed

lemma pomocna_lema_2:
  fixes a b c :: real
  assumes "a > 0" "b > 0" "c > 0"
  shows "a^2 * b^2 + b^2 * c^2 + c^2 * a^2 \<ge> a^2 * b * c + a * b^2 * c + a * b * c^2"
proof -
  have "a^2 * b^2 + a^2 * c^2 \<ge> 2 * a^2 * b * c"
    using assms AM_GM_nejednakost_2
    by simp

  moreover
  have "b^2 * a^2 + b^2 * c^2 \<ge> 2 * a * b^2 * c"
    using assms AM_GM_nejednakost_2
    by (metis (mono_tags, opaque_lifting) L2_set_mult_ineq_lemma ab_semigroup_mult_class.mult_ac(1) mult.commute power2_eq_square power_mult_distrib)
   
  moreover
  have "c^2 * a^2 + c^2 * b^2 \<ge> 2 * c^2 * a * b"
    using assms AM_GM_nejednakost_2
    by simp

  ultimately
  have "(a^2 * b^2 + a^2 * c^2) + (b^2 * a^2 + b^2 * c^2) + (c^2 * a^2 + c^2 * b^2) \<ge>  2 * a^2 * b * c + 2 * a * b^2 * c + 2 * c^2 * a * b"
    by linarith
  then have "a^2 * b^2 + c^2 * a^2 + a^2 * b^2 + b^2 * c^2 + c^2 * a^2 + b^2 * c^2 \<ge>  2 * a^2 * b * c + 2 * a * b^2 * c + 2 * c^2 * a * b"
    by auto
  then have "a^2 * b^2 + c^2 * a^2 + a^2 * b^2 + b^2 * c^2 + c^2 * a^2 + b^2 * c^2 \<ge>  2 * a^2 * b * c + 2 * a * b^2 * c + 2 * a * b * c^2"
    by (metis (no_types, opaque_lifting) ab_semigroup_mult_class.mult_ac(1) mult.commute)
  then have "(a^2 * b^2 + a^2 * b^2) + (b^2 * c^2 + b^2 * c^2) + (c^2 * a^2 + c^2 * a^2) \<ge> 2 * a^2 * b * c + 2 * a * b^2 * c + 2 * a * b * c^2"
    by auto
  then have "2 * a^2 * b^2 + 2 * b^2 * c^2 + 2 * c^2 * a^2 \<ge> 2 * a^2 * b * c + 2 * a * b^2 * c + 2 * a * b * c^2"
    by (simp add: algebra_simps)
  then have "2 * (a^2 * b^2 + b^2 * c^2 + c^2 * a^2) \<ge> 2 * a^2 * b * c + 2 * a * b^2 * c + 2 * a * b * c^2"
    by simp
  then have "2 * (a^2 * b^2 + b^2 * c^2 + c^2 * a^2) \<ge> 2 * (a^2 * b * c + a * b^2 * c + a * b * c^2)"
    by simp
  then show ?thesis by simp
qed

(* am-gm nejednakost *)
lemma pomocna_lema_3:
  fixes a b c :: real
  assumes "a > 0" "b > 0" "c > 0"
  shows "a^2 * b + a^2 * c + b^2 * a + b^2 * c + c^2 * a + c^2 * b \<ge> 6 * a * b * c"
  sorry 
  (* (a^2 * b + a^2 * c + b^2 * a + b^2 * c + c^2 * a + c^2 * b) / 6 \<ge> root 6 (a^2 * b * a^2 * c * b^2 * a * b^2 * c * c^2 * a * c^2 * b) = root 6 ((a * b * c)^6) = a * b * c *) 
                                                                             
theorem centralno_tvrdjenje:
  fixes a b c :: real
  assumes "a > 0" "b > 0" "c > 0"
  assumes "1 / a + 1 / b + 1 / c = a + b + c"
  shows "1 / (2*a + b + c)^2 + 1 / (2*b + c + a)^2 + 1 / (2*c + a + b)^2 \<le> 3/16"
proof -

  have #:"1 / (2*a + b + c)^2 + 1 / (2*b + c + a)^2 + 1 / (2*c + a + b)^2 \<le> (a + b + c) / (2 * (a + b) * (b + c) * (c + a))"
  proof -
    have "1 / (2*a + b + c)^2 + 1 / (2*b + c + a)^2 + 1 / (2*c + a + b)^2 \<le> 1 / (4 * (a + b)* (a + c)) + 1 / (4 * (b + c) * (b + a)) + 1 / (4 * (c + a) * (c + b))"
      using assms pomocna_lema
      by (smt (verit, del_insts))
    also have "... = (b + c) / (4 * (a + b) * (a + c) * (b + c)) + (a + c) / (4 * (b + c) * (b + a) * (a + c)) + (a + b) / (4 * (c + a) * (c + b) * (a + b))"
      using assms
      by auto
    also have "... = ((b + c) + (a + c) + (a + b)) / (4 * (a + b) * (b + c) * (c + a))"
      by (metis (no_types, opaque_lifting) add.commute add_divide_distrib mult.commute mult.left_commute)
    also have "... = (2 * a + 2 * b + 2 * c) / (4 * (a + b) * (b + c) * (c + a))"
      by simp
    also have "... = (2 * (a + b + c)) / (4 * (a + b) * (b + c) * (c + a))"
      by simp
    also have "... = (a + b + c) / (2 * (a + b) * (b + c) * (c + a))"
      by (metis divide_divide_eq_left' divide_divide_eq_right num_double numeral_times_numeral real_divide_square_eq)
    finally show ?thesis .
  qed

  moreover
  have ##:"a * b + b * c + c * a = a * b * c * (a + b + c)"
  proof -
    have "(b * c + a * c + a * b) / (a * b * c) = a + b + c"
      using assms
      by (simp add: add_frac_eq distrib_right)
    then show ?thesis
      using assms
      by (smt (verit, del_insts) add.commute divide_eq_0_iff mult.commute nonzero_mult_div_cancel_left times_divide_eq_right)
  qed

  moreover
  have ###:"(a * b + b * c + c * a)^2 \<ge> 3 * a * b * c * (a + b + c)"
  proof -

    have "(a * b + b * c + c * a)^2 =  a^2 * b^2 + b^2 * c^2 + c^2 * a^2 + 2 * a^2 * b * c + 2 * a * b^2 * c + 2 * a * b * c^2"
    proof -
      have "(a * b + b * c + c * a)^2 = (a * b + b * c)^2 + 2 * (a * b + b * c) * c * a + (c * a)^2"
        by (simp add: power2_sum)
      also have "... = (a * b + b * c)^2 + 2 * (a * b + b * c) * c * a + c ^ 2 * a ^ 2"
        by (simp add: power_mult_distrib)
      also have "... = (a * b)^2 + 2 * a * b * b * c + (b*c)^2 + 2 * (a * b + b * c) * c * a + c^2 * a^2"
        by (simp add: power2_sum)
      also have "... = a^2 * b^2 + 2 * a * b^2 * c + b^2 * c^2 + 2 * (a * b + b * c) * c * a + c^2 * a^2"
        by (simp add: power2_eq_square)
      also have "... = a^2 * b^2 + 2 * a * b^2 * c + b^2 * c^2 + (2 * a * b + 2 * b * c) * a * c + c^2 * a^2"
        by auto
      also have "... = a^2 * b^2 + 2 * a * b^2 * c + b^2 * c^2 + 2 * a * b * a * c + 2 * b * c * a * c + c^2 * a^2"
        by (simp add: ring_class.ring_distribs(2))
      also have "... =  a^2 * b^2 + 2 * a * b^2 * c + b^2 * c^2 + 2 * a*a * b * c + 2 * a * b * c*c + c^2 * a^2"
        by auto
      also have "... =  a^2 * b^2 + 2 * a * b^2 * c + b^2 * c^2 + 2 * a^2 * b * c + 2 * a * b * c^2 + c^2 * a^2"
        by (simp add: power2_eq_square)
      finally show ?thesis by simp
    qed

    moreover
    have "3 * a * b * c * (a + b + c) = a^2 * b * c + a * b^2 * c + a * b * c^2 + 2 * a^2 * b * c + 2 * a * b^2 * c + 2 * a * b * c^2"
    proof -
      have "3 * a * b * c * (a + b + c) = 3 * a * a * b * c + 3 * a * b * b * c + 3 * a * b * c * c"
        by (simp add: ring_class.ring_distribs(1))
      also have "... = 3 * a^2 * b * c + 3 * a * b^2 * c + 3 * a * b * c^2"
        by (simp add: power2_eq_square)
      also have "... = (a^2 * b * c + 2 * a^2 * b * c) + (a * b^2 * c + 2 * a * b^2 * c) + (a * b * c^2 + 2 * a * b * c^2)"
        by auto
      finally show ?thesis by simp
    qed

    ultimately show ?thesis 
      using pomocna_lema_2
      using assms
      by (smt (verit, best))
  qed

  moreover
  have ####:"9 * (a + b) * (b + c) * (c + a) \<ge> 8 * (a + b + c) * (a * b + b * c + c * a)"
  proof -
    have "8 * (a + b + c) * (a * b + b * c + c * a) = (8 * a + 8 * b + 8 * c) * (a * b + b * c + c * a)"
      by simp
    also have "... = 8 * a * (a * b + b * c + c * a) + 8 * b * (a * b + b * c + c * a) + 8 * c * (a * b + b * c + c * a)"
      by (simp add: distrib_right)
    also have "... =  8 * (a * a * b + a * b * c  + a * c * a) + 8 * (b * a * b + b * b * c + b * c * a) + 8 * (c * a * b + c * b * c + c * c * a)"
      by (simp add: distrib_left)
    also have "... = 8 * (a^2 * b + a * b * c + a^2 * c) + 8 * (b^2 * a + b^2 * c + a * b * c) + 8 * (a * b * c + c^2 * a + c^2 * b)"
      by (simp add: power2_eq_square)
    also have "... = 8 * (a^2 * b + a^2 * c + b^2 * a + b^2 * c + c^2 * a + c^2 * b) + 24 * a * b * c"
      by simp
    also have "... \<le> 9 * (a^2 * b + a^2 * c + b^2 * a + b^2 * c + c^2 * a + c^2 * b) + 18 * a * b * c"
      using assms pomocna_lema_3
      by (auto simp add: algebra_simps)
    also have "... = 9 * (a * b * c + a * c^2 + b^2 * c + b * c^2 + a^2 * b + a^2 * c + a * b^2 + a * b * c)"
      by simp
    also have "... = 9 * ((a * b + a * c + b^2 + b * c) * c + a^2 * b + a^2 * c + a * b^2 + a * b * c)"
      by (smt (verit, del_insts) ab_semigroup_mult_class.mult_ac(1) add.commute combine_common_factor distrib_left distrib_right group_cancel.add2 is_num_normalize(1) mult.commute mult.left_commute power2_eq_square)
    also have "... = 9 * ((a * b + a * c + b^2 + b * c) * c + a * b * a + a * c * a + b^2 * a + b * c * a)"
      by (simp add: power2_eq_square)
    also have "... = 9 * ((a * b + a * c + b^2 + b * c) * c + (a * b + a * c + b^2 + b * c) * a)"
      by (auto simp add: algebra_simps)
    also have "... = 9 * (a * b + a * c + b^2 + b * c) * (c + a)"
      by (auto simp add: algebra_simps)
    also have "... = 9 * (a * (b + c) + b * (b + c)) * (c + a)"
      by (smt (verit) add.commute combine_common_factor distrib_left distrib_right power2_eq_square)
    also have "... = 9 * (a + b) * (b + c) * (c + a)"
      by (auto simp add: algebra_simps)
    finally show ?thesis .
  qed

  moreover
  have "(a + b + c) / (2 * (a + b) * (b + c) * (c + a)) \<le> 3/16"
  proof -
    have  "(a + b + c) / (2 * (a + b) * (b + c) * (c + a)) = (((a + b + c) * (a * b + b * c + c * a)) / (2 * (a + b) * (b + c) * (c + a))) * (1  / (a * b * c * (a + b + c)))"
      using ##
      by auto
    also have " ... = (((a + b + c) * (a * b + b * c + c * a)) / (2 * (a + b) * (b + c) * (c + a))) * ((a * b + b * c + c * a) / (a * b * c * (a + b + c))) * (a * b * c * (a + b + c) / ((a * b + b * c + c * a)^2))"
      using assms ##
      by (simp add: power2_eq_square)
    also have "... = (((a + b + c) * (a * b + b * c + c * a)) / (2 * (a + b) * (b + c) * (c + a))) * ((a * b * c * (a + b + c)) / ((a * b + b * c + c * a)^2))"
      using ##
      by auto
    also have "... \<le> (((a + b + c) * (a * b + b * c + c * a)) / (2 * (a + b) * (b + c) * (c + a))) * ((a * b * c * (a + b + c)) / (3 * (a * b * c * (a + b + c))))"
    proof -     
      have $:"((a * b * c * (a + b + c)) / ((a * b + b * c + c * a)^2)) \<le>  ((a * b * c * (a + b + c)) / (3 * (a * b * c * (a + b + c))))"
        using assms ##  ### pomocna_kolicnik_2[of "(a * b + b * c + c * a)^2" "3 * a * b * c * (a + b + c)" "(a * b * c * (a + b + c))"] 
        by auto

      have "(((a + b + c) * (a * b + b * c + c * a)) / (2 * (a + b) * (b + c) * (c + a))) > 0"
        using assms
        by (smt (verit) divide_pos_pos mult_pos_pos)

      with $ show ?thesis
        using manje_proizvod[of "(((a + b + c) * (a * b + b * c + c * a)) / (2 * (a + b) * (b + c) * (c + a)))" "((a * b * c * (a + b + c)) / ((a * b + b * c + c * a)^2))"  "((a * b * c * (a + b + c)) / (3 * a * b * c * (a + b + c)))"]
        by auto
    qed
    also have "... = (((a + b + c) * (a * b + b * c + c * a)) / (2 * (a + b) * (b + c) * (c + a))) * 1/3 * ((a * b * c * (a + b + c)) / (a * b * c * (a + b + c)))"
      by auto
    also have "... = (((a + b + c) * (a * b + b * c + c * a)) / (2 * (a + b) * (b + c) * (c + a))) * 1/3"
      by (simp add: "##")
    also have "... = ((1/8 * 8 *(a + b + c) * (a * b + b * c + c * a)) / (2 * (a + b) * (b + c) * (c + a))) * 1/3"
      by auto
    also have "... \<le> ((1/8 * 9 * (a + b) * (b + c) * (c + a)) / (2 * (a + b) * (b + c) * (c + a))) * 1/3"
    proof -
      have "1/8 * 8 * (a + b + c) * (a * b + b * c + c * a) \<le> 1/8 * 9 * (a + b) * (b + c) * (c + a)"
        using ####
        by (auto simp add: algebra_simps)
      then have "1/8 * 8 * (a + b + c) * (a * b + b * c + c * a) / (2 * (a + b) * (b + c) * (c + a)) \<le> 1/8 * 9 * (a + b) * (b + c) * (c + a) / (2 * (a + b) * (b + c) * (c + a))"
        using assms pomocna_kolicnik_3[of "2 * (a + b) * (b + c) * (c + a)" "1/8 * 8 * (a + b + c) * (a * b + b * c + c * a)" "1/8 * 9 * (a + b) * (b + c) * (c + a)"]
        by auto
      then show ?thesis
        by simp
    qed
    also have "... = 1/8 *((9 * (a + b) * (b + c) * (c + a)) / (2 * (a + b) * (b + c) * (c + a))) * 1/3"
      using times_divide_eq_right[of "1/8" "9 * (a + b) * (b + c) * (c + a)" "2 * (a + b) * (b + c) * (c + a)"]
      by auto
    also have "... = 1/8 * 9 * (((a + b) * (b + c) * (c + a)) / (2 * (a + b) * (b + c) * (c + a))) * 1/3"
      by auto
    also have "... = 1/8 * 9 * 1/2 * (((a + b) * (b + c) * (c + a)) / ((a + b) * (b + c) * (c + a))) * 1/3"
      by auto
    also have "... = 1/8 * 9 * 1/2 * 1/3"
      using assms
      by force
    also have "... = 9/48"
      by simp
    also have "... = 3/16"
      by simp
    finally show ?thesis .
  qed
        
  ultimately
  show ?thesis 
    by linarith
      
qed      
     
end