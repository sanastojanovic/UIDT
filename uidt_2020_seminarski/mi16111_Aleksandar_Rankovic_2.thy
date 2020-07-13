theory mi16111_Aleksandar_Rankovic_2
  imports Complex_Main
begin

(*Link na zadatak:  https://imomath.com/srb/zadaci/BIH_2012_bihmo_resenja.pdf zadatak I-2 *)


(*Zelimo da pokazemo da vazi ovo:
  a ^ 3 / (b ^ 2 + c) + b ^ 3 / (c ^ 2 + a) + c ^ 3 / (a ^ 2 + b) \<ge> (root 3) / (1 + root 3)
za date uslove:
  a > 0, b > 0, c > 0, a ^ 2 + b ^ 2 + c ^ 2 = 1  *)

(* pomocne generalne lemme *)
lemma ocigledno:
  fixes x1 x2 x3 :: real
  assumes "x1>0" "x2>0" "x3>0"
  shows "x1^2 + x2^2 + x3^2 > 0"
  using assms
  by (meson pos_add_strict zero_less_power)

lemma koren_kv:
  fixes a::real
  assumes "a > 0"
  shows "a = (root 2 a)^2"
  using assms
  by simp

lemma koren_kv_2:
  fixes a::real
  assumes "a > 0"
  shows "a = root 2 (a^2)"
  using assms
  using real_root_power_cancel by auto


lemma kvadrat_binoma:
  fixes a b :: real
  shows "(a - b)^2 = a^2 - 2*a*b + b^2"
proof-
  have "(a - b)^2 = (a - b)*(a - b)"
    by (simp add: power2_eq_square)
  also have "... = a^2 - a*b - b*a + b^2"
    by (metis (no_types, hide_lams) add.commute add_diff_eq diff_diff_eq2 eq_diff_eq mult_diff_mult power2_eq_square right_diff_distrib')
  finally show ?thesis
    by auto
qed

lemma kvadrat_binoma_2:
  fixes a b :: real
  shows "(a + b)^2 = a^2 + 2*a*b + b^2"
proof-
  have "(a + b)^2 = (a + b)*(a + b)"
    by (simp add: power2_eq_square)
  also have "... = a^2 + a*b + b*a + b^2"
    by (simp add: distrib_left distrib_right power2_eq_square)
  finally show ?thesis
    by auto
qed

lemma kvadrat_je_pozitivan:
  fixes y1 y2 y3 :: real
  assumes "y1>0" "y2>0" "y3>0"
  shows "y1^2 + y2^2 + y3^2 > 0"
  by (simp add: assms(1) assms(2) assms(3) ocigledno)

(* Pomocne lemme za obicnu  kosi nejednakost *)
lemma pom_za_kn:
  fixes x1 x2 x3 y1 y2 y3 :: real
  assumes "x1 > 0" "x2 > 0" "x3 > 0"  "y1 > 0" "y2 > 0" "y3 > 0"
  shows "x1^2*y2^2 + x2^2*y1^2 + x1^2*y3^2 + x3^2*y1^2 + x2^2*y3^2 + x3^2*y2^2 \<ge> 2*x1*y1*x2*y2 +  2*x1*y1*x3*y3 +  2*x2*y2*x3*y3"
proof-
  have "(x1*y2 - x2*y1)^2 + (x1*y3 - x3*y1)^2 + (x2*y3 - x3*y2)^2 \<ge> 0"
    by auto
  then have "(x1*y2)^2 - 2*(x1*y2)*(x2*y1) + (x2*y1)^2 + (x1*y3)^2 - 2*(x1*y3)*(x3*y1) + (x3*y1)^2 + (x2*y3)^2 - 2*(x2*y3)*(x3*y2) + (x3*y2)^2 \<ge> 0"
    using kvadrat_binoma [of "x1*y2" "x2*y1"]
    using kvadrat_binoma [of "x1*y3" "x3*y1"]
    using kvadrat_binoma [of "x2*y3" "x3*y2"]
    by linarith
  then have "(x1*y2)^2 + (x2*y1)^2 + (x1*y3)^2 + (x3*y1)^2 + (x2*y3)^2 + (x3*y2)^2 \<ge>  2*(x1*y2)*(x2*y1) + 2*(x1*y3)*(x3*y1) + 2*(x2*y3)*(x3*y2)"
    by auto
  then show ?thesis
    by (metis (mono_tags, hide_lams) ab_semigroup_mult_class.mult_ac(1) add.commute group_cancel.add2 mult.commute mult.left_commute power_mult_distrib)
qed

lemma leva_strana_kn:
  fixes x1 x2 x3 y1 y2 y3 :: real
  assumes "x1 > 0" "x2 > 0" "x3 > 0"  "y1 > 0" "y2 > 0" "y3 > 0"
  shows "x1^2*y1^2 + x2^2*y2^2 + x3^2*y3^2 + x1^2*y2^2 + x2^2*y1^2 + x1^2*y3^2 + x3^2*y1^2 + x2^2*y3^2 + x3^2*y2^2 = (x1^2 + x2^2 + x3^2) * (y1^2 + y2^2 + y3^2)"
    by (simp add: add.left_commute distrib_left distrib_right)  

lemma distribuiranost:
  fixes x1 x2 x3 y1 y2 y3 :: real
  assumes "x1 > 0" "x2 > 0" "x3 > 0"  "y1 > 0" "y2 > 0" "y3 > 0"
  shows "2*(x1*y1 + x2*y2)*x3*y3 = 2*(x1*y1)*(x3*y3) + 2*(x2*y2)*(x3*y3)"
  using distrib_right [of "x1*y1" "x2*y2" "x3*y3"]
  by linarith

lemma desna_strana_kn:
  fixes x1 x2 x3 y1 y2 y3 :: real
  assumes "x1 > 0" "x2 > 0" "x3 > 0"  "y1 > 0" "y2 > 0" "y3 > 0"
  shows "x1^2*y1^2 + x2^2*y2^2 + x3^2*y3^2 + 2*x1*y1*x2*y2 +  2*x1*y1*x3*y3 +  2*x2*y2*x3*y3 = (x1*y1 + x2*y2 + x3*y3)^2"
proof-
  have "(x1*y1 + x2*y2 + x3*y3)^2 = (x1*y1 + x2*y2)^2 + 2*(x1*y1 + x2*y2)*x3*y3 + (x3*y3)^2"
    using kvadrat_binoma_2
    by simp
  also have "... = (x1*y1)^2 + 2*(x1*y1)*(x2*y2) + (x2*y2)^2 + 2*(x1*y1 + x2*y2)*x3*y3 + (x3*y3)^2"
    using kvadrat_binoma_2
    by simp
  also have "... =  (x1*y1)^2 + 2*x1*y1*x2*y2 + (x2*y2)^2 + 2*(x1*y1)*(x3*y3) + 2*(x2*y2)*x3*y3 + (x3*y3)^2"
    using distribuiranost [of x1 x2 x3 y1 y2 y3]
    by (simp add: mult.commute ring_class.ring_distribs(1))   
  finally show ?thesis
    using algebra_simps
    by (simp add: power_mult_distrib)
qed

(* obicna kosi_nejednakost *)
lemma kosi_nejed:
  fixes x1 x2 x3 y1 y2 y3 :: real
  assumes "x1 > 0" "x2 > 0" "x3 > 0"  "y1 > 0" "y2 > 0" "y3 > 0"
  shows "(x1^2 + x2^2 + x3^2) * (y1^2 + y2^2 + y3^2) \<ge> (x1*y1 + x2*y2 + x3*y3)^2"
proof-
  have "x1^2*y2^2 + x2^2*y1^2 + x1^2*y3^2 + x3^2*y1^2 + x2^2*y3^2 + x3^2*y2^2 \<ge> 2*x1*y1*x2*y2 +  2*x1*y1*x3*y3 +  2*x2*y2*x3*y3"
    using pom_za_kn
    by (simp add: assms(1) assms(2) assms(3) assms(4) assms(5) assms(6))
  then have "x1^2*y1^2 + x2^2*y2^2 + x3^2*y3^2 + x1^2*y2^2 + x2^2*y1^2 + x1^2*y3^2 + x3^2*y1^2 + x2^2*y3^2 + x3^2*y2^2 \<ge> x1^2*y1^2 + x2^2*y2^2 + x3^2*y3^2 + 2*x1*y1*x2*y2 +  2*x1*y1*x3*y3 +  2*x2*y2*x3*y3"
    by auto
  then have "(x1^2 + x2^2 + x3^2) * (y1^2 + y2^2 + y3^2) \<ge> x1^2*y1^2 + x2^2*y2^2 + x3^2*y3^2 + 2*x1*y1*x2*y2 +  2*x1*y1*x3*y3 +  2*x2*y2*x3*y3"
    using leva_strana_kn [of x1 x2 x3 y1 y2 y3]
    using assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) by auto
  then show ?thesis
    using desna_strana_kn [of x1 x2 x3 y1 y2 y3]
    by (simp add: assms(1) assms(2) assms(3) assms(4) assms(5) assms(6))
qed

(* Pomocne lemme za kosi_nejednakost_1 *)
lemma pom_kosi_1 [simp]:
  fixes a b c::real
  assumes "a > 0" "b > 0" "c > 0" "a ^ 2 + b ^ 2 + c ^ 2 = 1"
  shows "(root 2 (a*(b ^ 2 + c))) > 0"
  by (simp add: add.commute add_pos_nonneg assms(1) assms(3))

lemma pom_kosi_2 [simp]:
  fixes a b c::real
  assumes "a > 0" "b > 0" "c > 0" "a ^ 2 + b ^ 2 + c ^ 2 = 1"
  shows "(root 2 (a ^ 3 / (b ^ 2 + c))) > 0"
  by (metis add.commute add_cancel_right_right add_pos_pos assms(1) assms(3) divide_pos_pos pos2 real_root_gt_zero zero_eq_power2 zero_less_power zero_less_power2)

lemma kn1l_pom_1:
  fixes a b c::real
  assumes "a > 0" "b > 0" "c > 0"
  shows "(a*(b ^ 2 + c)) > 0"
  by (simp add: add_pos_pos assms(1) assms(2) assms(3) power2_eq_square)

lemma kn1l_pom_2:
  fixes a b c::real
  assumes "a > 0" "b > 0" "c > 0"
  shows "(a ^ 3 / (b ^ 2 + c)) > 0"
  by (meson add_pos_pos assms(1) assms(2) assms(3) divide_pos_pos zero_less_power)

lemma kn_1_leva:
  fixes a b c::real
  assumes "a > 0" "b > 0" "c > 0" "a ^ 2 + b ^ 2 + c ^ 2 = 1"
  shows "((root 2 (a*(b ^ 2 + c)))^2 + (root 2 (b*(c ^ 2 + a)))^2 + (root 2 (c*(a ^ 2 + b)))^2)*((root 2 (a ^ 3 / (b ^ 2 + c)))^2 + (root 2 (b ^ 3 / (c ^ 2 + a)))^2 + (root 2 (c ^ 3 / (a ^ 2 + b)))^2) = ((a*(b ^ 2 + c)) + (b*(c ^ 2 + a)) + (c*(a ^ 2 + b)))*((a ^ 3 / (b ^ 2 + c)) + (b ^ 3 / (c ^ 2 + a)) + (c ^ 3 / (a ^ 2 + b)))"
proof-
  have "((root 2 (a*(b ^ 2 + c)))^2 + (root 2 (b*(c ^ 2 + a)))^2 + (root 2 (c*(a ^ 2 + b)))^2)*((root 2 (a ^ 3 / (b ^ 2 + c)))^2 + (root 2 (b ^ 3 / (c ^ 2 + a)))^2 + (root 2 (c ^ 3 / (a ^ 2 + b)))^2) =((a*(b ^ 2 + c)) + (b*(c ^ 2 + a)) + (c*(a ^ 2 + b)))*((root 2 (a ^ 3 / (b ^ 2 + c)))^2 + (root 2 (b ^ 3 / (c ^ 2 + a)))^2 + (root 2 (c ^ 3 / (a ^ 2 + b)))^2) "
    using kn1l_pom_1 [of a b c]
    using koren_kv [of "(a*(b ^ 2 + c))"]
    using kn1l_pom_1 [of b c a]
    using koren_kv [of "(b*(c ^ 2 + a))"] 
    using kn1l_pom_1 [of c a b]
    using koren_kv [of "(c*(a ^ 2 + b))"]
    using assms(1) assms(2) assms(3) by auto
  also have "... = ((a*(b ^ 2 + c)) + (b*(c ^ 2 + a)) + (c*(a ^ 2 + b)))*((a ^ 3 / (b ^ 2 + c)) + (b ^ 3 / (c ^ 2 + a)) + (c ^ 3 / (a ^ 2 + b)))"
    using kn1l_pom_2 [of a b c]
    using koren_kv [of "(a ^ 3 / (b ^ 2 + c))"]
    using kn1l_pom_2 [of b c a]
    using koren_kv [of "(b ^ 3 / (c ^ 2 + a))"]
    using kn1l_pom_2 [of c a b]
    using koren_kv [of "(c ^ 3 / (a ^ 2 + b))"]
    using assms(1) assms(2) assms(3) by auto
  finally show ?thesis
    .
qed

lemma simpanje:
  fixes a b c ::real
  assumes "a > 0" "b > 0" "c > 0"
  shows "a ^ 2 = (root 2 (a*(b ^ 2 + c)))*(root 2 (a ^ 3 / (b ^ 2 + c)))"
  by (smt assms(1) assms(2) assms(3) koren_kv nonzero_mult_div_cancel_right ocigledno power2_eq_square power3_eq_cube real_root_mult times_divide_eq_left times_divide_eq_right)

lemma kn_2_desna:
 fixes a b c::real
 assumes "a > 0" "b > 0" "c > 0" "a ^ 2 + b ^ 2 + c ^ 2 = 1"
 shows "((root 2 (a*(b ^ 2 + c)))*(root 2 (a ^ 3 / (b ^ 2 + c))) + (root 2 (b*(c ^ 2 + a)))*(root 2 (b ^ 3 / (c ^ 2 + a))) + (root 2 (c*(a ^ 2 + b)))*(root 2 (c ^ 3 / (a ^ 2 + b))))^2 = (a ^ 2 + b ^ 2 + c ^ 2) ^ 2"
  using simpanje
  by (metis assms(1) assms(2) assms(3))

(*Prvo ustanovimo na osnovu kosijeve nejednakosti *)
lemma kosi_nejednakost_1:  
  fixes a b c::real
  assumes "a > 0" "b > 0" "c > 0" "a ^ 2 + b ^ 2 + c ^ 2 = 1"
  shows "(a*(b ^ 2 + c) + b*(c ^ 2 + a) + c*(a ^ 2 + b))*(a ^ 3 / (b ^ 2 + c) + b ^ 3 / (c ^ 2 + a) + c ^ 3 / (a ^ 2 + b)) \<ge> (a ^ 2 + b ^ 2 + c ^ 2) ^ 2"
proof-
  have "((root 2 (a*(b ^ 2 + c)))^2 + (root 2 (b*(c ^ 2 + a)))^2 + (root 2 (c*(a ^ 2 + b)))^2)*((root 2 (a ^ 3 / (b ^ 2 + c)))^2 + (root 2 (b ^ 3 / (c ^ 2 + a)))^2 + (root 2 (c ^ 3 / (a ^ 2 + b)))^2) \<ge> ((root 2 (a*(b ^ 2 + c)))*(root 2 (a ^ 3 / (b ^ 2 + c))) + (root 2 (b*(c ^ 2 + a)))*(root 2 (b ^ 3 / (c ^ 2 + a))) + (root 2 (c*(a ^ 2 + b)))*(root 2 (c ^ 3 / (a ^ 2 + b))))^2"
    using pom_kosi_1 [of a b c]
    using  pom_kosi_2 [ of a b c]
     using pom_kosi_1 [of b c a]
     using  pom_kosi_2 [ of b c a]
     using pom_kosi_1 [of c a b]
    using  pom_kosi_2 [ of c a b]
    using kosi_nejed [of "(root 2 (a*(b ^ 2 + c)))" "(root 2 (b*(c ^ 2 + a)))" "(root 2 (c*(a ^ 2 + b)))" "(root 2 (a ^ 3 / (b ^ 2 + c)))" "(root 2 (b ^ 3 / (c ^ 2 + a)))" "(root 2 (c ^ 3 / (a ^ 2 + b)))"]
    using assms(1) assms(2) assms(3) assms(4) by auto
  then have "((a*(b ^ 2 + c)) + (b*(c ^ 2 + a)) + (c*(a ^ 2 + b)))*((a ^ 3 / (b ^ 2 + c)) + (b ^ 3 / (c ^ 2 + a)) + (c ^ 3 / (a ^ 2 + b))) \<ge> ((root 2 (a*(b ^ 2 + c)))*(root 2 (a ^ 3 / (b ^ 2 + c))) + (root 2 (b*(c ^ 2 + a)))*(root 2 (b ^ 3 / (c ^ 2 + a))) + (root 2 (c*(a ^ 2 + b)))*(root 2 (c ^ 3 / (a ^ 2 + b))))^2"
    by (metis assms(1) assms(2) assms(3) assms(4) kn_1_leva)
  then show ?thesis  
    by (simp add: assms(1) assms(2) assms(3) assms(4) kn_2_desna)
  qed

(* na osnovu lemme preformulisan_pocetak koja se nalazi malo ispod zelimo da dokazemo:
"a*b^2 + b*c^2 + c*a^2 + a*c + b*a + c*b \<le> (1 / (root 2 3)) + 1" *)
(* pokazimo da je *)
lemma zbir_manji_od_kvadrata:  
  fixes a b c::real
  shows "a*b + b*c + c*a \<le> a^2 + b^2 + c^2"
  proof-
  have "0 \<le> (a - b)^2 + (b - c)^2 + (c-a)^2"
    by simp
  also have "... = (a^2 - 2*a*b + b^2) + (b^2 - 2*b*c + c^2) + (c^2 - 2*c*a + a^2)"
    using kvadrat_binoma
    by auto
  also have "... = 2*a^2 +  2*b^2 +  2*c^2 + -2*a*b - 2*b*c - 2*c*a"
    by auto
  finally show ?thesis
    by simp
qed
(* koristeci  a^2 + b^2 + c^2 = 1 ostaje nam samo a*b^2 + b*c^2 + c*a^2 \<le>  (1 / (root 3)) *)

(* primenimo kosijevu nejednakost opet *)
lemma kosi_nejednakost_2: 
  fixes a b c::real
  assumes "a > 0" "b > 0" "c > 0" "a ^ 2 + b ^ 2 + c ^ 2 = 1"
  shows "a*b^2 + b*c^2 + c*a^2 \<le> root 2 (( a^2 + b^2 + c^2 )*( a^2*b^2 + b^2*c^2 + c^2*a^2 ))"
proof-

  have "(b*(a*b) + c*(b*c) + a*(c*a))^2 \<le> ((b^2 + c^2 + a^2)*( a^2*b^2 + b^2*c^2 + c^2*a^2 ))"
    using kosi_nejed[of "b" "c" "a" "a*b" "b*c" "c*a"]
     by (simp add: assms(1) assms(2) assms(3) power_mult_distrib)
   then have "(a*b^2 + b*c^2 + c*a^2)^2 \<le> ((b^2 + c^2 + a^2)*( a^2*b^2 + b^2*c^2 + c^2*a^2 ))"
     by (simp add: mult.left_commute power2_eq_square)
   then have "root 2 ((a*b^2 + b*c^2 + c*a^2)^2) \<le> root 2 ((b^2 + c^2 + a^2)*( a^2*b^2 + b^2*c^2 + c^2*a^2 ))"
     by simp
  then show ?thesis
    using koren_kv_2
    by (smt pos2 power2_less_eq_zero_iff real_root_pos_pos real_root_pos_unique)
qed


(* POMOCNE LEMME ZA VREDI OVO *)
lemma pomocna_za_vredi_ovo:
  fixes a b c ::real
  shows  "a^2*b^2 + b^2*c^2 + c^2*a^2 \<le> (a ^ 4 + b ^ 4 + c ^ 4)"
proof-
  have "0 \<le> (a^2 - b^2)^2 + (b^2 - c^2)^2 + (c^2 - a^2)^2"
    by simp
  also have "... = ((a^2)^2 - 2*a^2*b^2 + (b^2)^2) +  ((b^2)^2 - 2*b^2*c^2 + (c^2)^2) +  ((c^2)^2 - 2*c^2*a^2 + (a^2)^2)"
    using kvadrat_binoma
    by auto
  also have "... = 2*a^4 +  2*b^4 +  2*c^4 - 2*a^2*b^2 - 2*b^2*c^2 - 2*c^2*a^2"
    by auto
  finally show ?thesis
    by auto
qed

lemma pomocna_za_vredi_ovo_2:
  fixes a b c :: real
  shows "(a ^ 2 + b ^ 2 + c ^ 2) ^ 2 = a ^ 4 + b ^ 4 + c ^ 4 + 2*a^2*b^2 + 2*a^2*c^2 + 2*b^2*c^2"
proof-
  have "(a ^ 2 + b ^ 2 + c ^ 2) ^ 2 = (a^2 + b^2)^2 + 2*(a^2 + b^2)*c^2 + (c^2)^2"
    by (simp add: power2_sum)
  also have "... = ((a^2)^2 + 2*a^2*b^2 + (b^2)^2) + 2*(a^2 + b^2)*c^2  + (c^2)^2"
    using kvadrat_binoma_2
    by simp
  also have "... = a ^ 4 + b ^ 4 + c ^ 4 + 2*a^2*b^2  + 2*(a^2 + b^2)*c^2"
    by auto
  also have "... = a ^ 4 + b ^ 4 + c ^ 4 + 2*a^2*b^2 + 2*a^2*c^2 + 2*b^2*c^2"
    by (smt left_diff_distrib')
  then show ?thesis
    by (simp add: calculation)  
qed

lemma pomocna_za_vredi_ovo_3:
  fixes a b c :: real
  shows "3*a^2*b^2 + 3*b^2*c^2 + 3*c^2*a^2 \<le> (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 \<longleftrightarrow> a^2*b^2 + b^2*c^2 + c^2*a^2 \<le> (a ^ 4 + b ^ 4 + c ^ 4)" (is "?l \<longleftrightarrow> ?d")
proof
  assume "?l"
  then have "3*a^2*b^2 + 3*b^2*c^2 + 3*c^2*a^2 \<le>  a ^ 4 + b ^ 4 + c ^ 4 + 2*a^2*b^2 + 2*a^2*c^2 + 2*b^2*c^2"
    using pomocna_za_vredi_ovo_2
    by simp
  show "?d"
    by (simp add: pomocna_za_vredi_ovo)
next
  assume "?d"
  then have "3*a^2*b^2 + 3*b^2*c^2 + 3*c^2*a^2 - 2*a^2*b^2 - 2*b^2*c^2 - 2*c^2*a^2  \<le> (a ^ 4 + b ^ 4 + c ^ 4)"
    by linarith
  then have "3*a^2*b^2 + 3*b^2*c^2 + 3*c^2*a^2 \<le> a ^ 4 + b ^ 4 + c ^ 4 + 2*a^2*b^2 + 2*b^2*c^2 + 2*c^2*a^2"    
    by simp
  then show "?l"
    using pomocna_za_vredi_ovo_2 by auto
qed

(* a to je tacno zato sto vazi sledece tvrdjenje *)
lemma vredi_ovo:
  fixes a b c::real
  shows  "3*a^2*b^2 + 3*b^2*c^2 + 3*c^2*a^2 \<le> (a ^ 2 + b ^ 2 + c ^ 2) ^ 2"
  using pomocna_za_vredi_ovo
  using pomocna_za_vredi_ovo_3
  by blast

(* koristeci  a^2 + b^2 + c^2 = 1 desna strana kosi_nejednakost_2 lemme postaje root ( a^2*b^2 + b^2*c^2 + c^2*a^2) *)
(* a*b^2 + b*c^2 + c*a^2 \<le>  root ( a^2*b^2 + b^2*c^2 + c^2*a^2) *)
(* pa je dovoljno pokazati root (a^2*b^2 + b^2*c^2 + c^2*a^2) \<le>  (1 / (root 3)) *)

lemma dovoljna: 
  fixes a b c::real
  assumes "a > 0" "b > 0" "c > 0" "a ^ 2 + b ^ 2 + c ^ 2 = 1"
  shows  "a^2*b^2 + b^2*c^2 + c^2*a^2 \<le>  (1 / 3)"
  proof-
  have "3*a^2*b^2 + 3*b^2*c^2 + 3*c^2*a^2 \<le> (a ^ 2 + b ^ 2 + c ^ 2) ^ 2"
    using vredi_ovo
    by auto
  then have "3*a^2*b^2 + 3*b^2*c^2 + 3*c^2*a^2 \<le> (1) ^ 2"
    using assms
    by simp
  then have "(3*a^2*b^2 + 3*b^2*c^2 + 3*c^2*a^2 ) / 3 \<le> ((1) ^ 2) / 3"
    by auto
  then show ?thesis
    by auto
qed

(*kako je a^2 + b^2 + c^2)^2 = 1 iz toga i kosi_nejednakosti_1
 uz pomoc malo pretumbavanja postane jasno da nam je dovoljno da dokazemo: *)
lemma preformulisan_pocetak: 
  fixes a b c::real
  assumes "a > 0" "b > 0" "c > 0" "a ^ 2 + b ^ 2 + c ^ 2 = 1"
  shows "a*b^2 + b*c^2 + c*a^2 + a*c + b*a + c*b \<le> (1 / (root 2 3)) + 1"
proof-
  have "a*b + b*c + c*a \<le> a^2 + b^2 + c^2"
    using zbir_manji_od_kvadrata
    by simp
  then have "a*b^2 + b*c^2 + c*a^2 \<le> root 2 (( a^2 + b^2 + c^2 )*( a^2*b^2 + b^2*c^2 + c^2*a^2 ))"
    using kosi_nejednakost_2
    by (simp add: assms(1) assms(2) assms(3) assms(4))
  then have "a*b^2 + b*c^2 + c*a^2 \<le> root 2 ((1)*( a^2*b^2 + b^2*c^2 + c^2*a^2 ))"
    using assms(4)
    by simp
  then have "a^2*b^2 + b^2*c^2 + c^2*a^2 \<le>  (1 / 3)"
    using dovoljna
    by (simp add: assms(1) assms(2) assms(3) assms(4))
  then have "root 2 ((1)*( a^2*b^2 + b^2*c^2 + c^2*a^2 )) \<le> root 2 (1 / 3)"
    by simp
  then show ?thesis
    by (smt \<open>a * b + b * c + c * a \<le> a\<^sup>2 + b\<^sup>2 + c\<^sup>2\<close> \<open>a * b\<^sup>2 + b * c\<^sup>2 + c * a\<^sup>2 \<le> root 2 (1 * (a\<^sup>2 * b\<^sup>2 + b\<^sup>2 * c\<^sup>2 + c\<^sup>2 * a\<^sup>2))\<close> add_gr_0 assms(4) mult.commute neq0_conv num.distinct(1) numeral_eq_one_iff one_add_one real_root_divide real_root_eq_1_iff)
qed

(* Pomocne lemme za glavnu nejednacinu *)
lemma pomocna_pozitivno:
  fixes a b c :: real
  assumes "a > 0" "b > 0" "c > 0" "a ^ 2 + b ^ 2 + c ^ 2 = 1"
  shows "(a*(b ^ 2 + c) + b*(c ^ 2 + a) + c*(a ^ 2 + b)) > 0"
   by (smt assms(1) assms(2) assms(3) mult_less_0_iff power2_less_0 real_mult_less_iff1)


lemma pomocni_uslov_za_glavnu:
  fixes a b c::real
  assumes "a > 0" "b > 0" "c > 0" "a ^ 2 + b ^ 2 + c ^ 2 = 1"
  shows "1/(a*(b ^ 2 + c) + b*(c ^ 2 + a) + c*(a ^ 2 + b)) \<ge> (root 2 3) / (1 + root 2 3)"
proof-
  have "a*b^2 + b*c^2 + c*a^2 + a*c + b*a + c*b \<le> (1 / (root 2 3)) + 1"
    using preformulisan_pocetak
    by (simp add: preformulisan_pocetak assms(1) assms(2) assms(3) assms(4))
  then have "(a*(b ^ 2 + c) + b*(c ^ 2 + a) + c*(a ^ 2 + b)) \<le>  (1 / (root 2 3)) + 1"
    using algebra_simps
    by (simp add: distrib_left)
  then have "(a*(b ^ 2 + c) + b*(c ^ 2 + a) + c*(a ^ 2 + b)) \<le>  1 / root 2 3 + (root 2 3)/(root 2 3)"
    by simp
  then have "(a*(b ^ 2 + c) + b*(c ^ 2 + a) + c*(a ^ 2 + b)) \<le>  ((1 + root 2 3)/(root 2 3))"
    by (simp add: add_divide_distrib)
  then have "(a*(b ^ 2 + c) + b*(c ^ 2 + a) + c*(a ^ 2 + b))/((1 + root 2 3)/(root 2 3)) \<le>  1"
    using pomocna_pozitivno
    by (smt divide_le_eq_1_pos pos2 real_root_gt_0_iff)
  then have "1/((1 + root 2 3)/(root 2 3)) \<le>  1/(a*(b ^ 2 + c) + b*(c ^ 2 + a) + c*(a ^ 2 + b))"
    using pomocna_pozitivno
    by (smt \<open>a * (b\<^sup>2 + c) + b * (c\<^sup>2 + a) + c * (a\<^sup>2 + b) \<le> (1 + root 2 3) / root 2 3\<close> assms(1) assms(2) assms(3) assms(4) frac_le)
  then show ?thesis
    using algebra_simps
    by (simp add: add_diff_eq)
qed
(* Nejednakost koju pokusavamo da dokazemo *)
lemma 
  fixes a b c::real
  assumes "a > 0" "b > 0" "c > 0" "a ^ 2 + b ^ 2 + c ^ 2 = 1"
  shows "a ^ 3 / (b ^ 2 + c) + b ^ 3 / (c ^ 2 + a) + c ^ 3 / (a ^ 2 + b) \<ge> (root 2 3) / (1 + root 2 3)"
  using assms
proof-
  have "(a*(b ^ 2 + c) + b*(c ^ 2 + a) + c*(a ^ 2 + b))*(a ^ 3 / (b ^ 2 + c) + b ^ 3 / (c ^ 2 + a) + c ^ 3 / (a ^ 2 + b)) \<ge> (a ^ 2 + b ^ 2 + c ^ 2) ^ 2"
    using kosi_nejednakost_1
    by (simp add: assms(1) assms(2) assms(3) assms(4))
  then have "(a*(b ^ 2 + c) + b*(c ^ 2 + a) + c*(a ^ 2 + b))*(a ^ 3 / (b ^ 2 + c) + b ^ 3 / (c ^ 2 + a) + c ^ 3 / (a ^ 2 + b)) \<ge> 1"
    by (simp add: assms(4))
  then have "(a*(b ^ 2 + c) + b*(c ^ 2 + a) + c*(a ^ 2 + b))*(a ^ 3 / (b ^ 2 + c) + b ^ 3 / (c ^ 2 + a) + c ^ 3 / (a ^ 2 + b))/(a*(b ^ 2 + c) + b*(c ^ 2 + a) + c*(a ^ 2 + b)) \<ge> 1/(a*(b ^ 2 + c) + b*(c ^ 2 + a) + c*(a ^ 2 + b))"
    using pomocna_pozitivno
    by (smt assms(1) assms(2) assms(3) assms(4) divide_le_cancel)
  then have "(a ^ 3 / (b ^ 2 + c) + b ^ 3 / (c ^ 2 + a) + c ^ 3 / (a ^ 2 + b)) \<ge> 1/(a*(b ^ 2 + c) + b*(c ^ 2 + a) + c*(a ^ 2 + b))"
    using pomocna_pozitivno
    using algebra_simps
    by (smt \<open>1 \<le> (a * (b\<^sup>2 + c) + b * (c\<^sup>2 + a) + c * (a\<^sup>2 + b)) * (a ^ 3 / (b\<^sup>2 + c) + b ^ 3 / (c\<^sup>2 + a) + c ^ 3 / (a\<^sup>2 + b))\<close> mult_not_zero nonzero_mult_div_cancel_left)
  then have "1/(a*(b ^ 2 + c) + b*(c ^ 2 + a) + c*(a ^ 2 + b)) \<ge> (root 2 3) / (1 + root 2 3)"
    using pomocni_uslov_za_glavnu
    by (simp add: assms(1) assms(2) assms(3) assms(4))
  then show ?thesis
    using \<open>1 / (a * (b\<^sup>2 + c) + b * (c\<^sup>2 + a) + c * (a\<^sup>2 + b)) \<le> a ^ 3 / (b\<^sup>2 + c) + b ^ 3 / (c\<^sup>2 + a) + c ^ 3 / (a\<^sup>2 + b)\<close> by auto
qed


end