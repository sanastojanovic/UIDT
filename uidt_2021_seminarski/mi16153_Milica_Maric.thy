theory mi16153_Milica_Maric
  imports Complex_Main
begin

text\<open>
https://www.imo-official.org/problems/IMO2010SL.pdf

Zadatak A2

Let the real numbers a, b, c, d satisfy the relations a + b + c + d = 6 and 
a\<^sup>2 + b\<^sup>2 + c\<^sup>2 + d\<^sup>2 = 12. Prove that 36 \<le> 4(a\<^sup>3 + b\<^sup>3 + c\<^sup>3 + d\<^sup>3) - (a\<^sup>4 + b\<^sup>4 + c\<^sup>4 + d\<^sup>4) \<le> 48 
\<close>


(*lemma a_na_2_b_na_2:
  fixes a b :: real
  shows "a*b*a*b = a^2*b^2"
proof-
  have "a*b*a*b = a*a*b*b"
    by auto
  also have "... = a^2*b^2"
    by (auto simp add: power2_eq_square)
  finally show ?thesis
    .
qed
*)

lemma razlika_sa_1_na_2:
  fixes a  :: real
  shows "(a-1)^2 = a^2 - 2*a + 1"
proof-
  have "(a-1)^2 = (a-1)*(a-1)"
    by (simp add: power2_eq_square)
  also have "... = a*a - a - a +1"
    by (simp add: algebra_simps)
  also have "... = a^2 - 2*a + 1"
    by (simp add: power2_eq_square)
  finally show ?thesis
    by auto
qed


lemma razlika_na_4:
  fixes a b :: real
  shows  "(a - b) ^ 4 = a ^ 4 - 4*a^3*b + 6*a^2*b^2 - 4*a*b^3+ b^4"
proof-
  have "(a - b)^4 = (a-b)^2 * (a-b)^2"
    by auto
  also have "... =(a^2 - 2*a*b + b^2)*(a^2 - 2*a*b + b^2)"
    by (smt (verit) power2_diff)
  also have "... = a ^ 4 - 2*a^2*a*b + a^2*b^2 - 2*a*b*a^2 + 2*a*b*2*a*b - 2*a*b*b^2+ b^2*a^2  - b^2*2*a*b +  b^4"
    by (auto simp add: algebra_simps)
  also have "... = a ^ 4 - 2*a^3*b + a^2*b^2 - 2*a*b*a^2 + 4*a*b*a*b - 2*a*b^3+ b^2*a^2  - b^3*2*a +  b^4"
    by (simp add: power2_eq_square power3_eq_cube)
  also have "... =  a ^ 4 - 2*a^3*b + a^2*b^2 - 2*b*a^3 + 4*a^2*b^2 - 2*a*b^3+ b^2*a^2  - 2* b^3*a +  b^4"
    by (auto simp add: power2_eq_square power3_eq_cube algebra_simps)
  also have "... = a^4  - 2*a^3*b + a^2*b^2 - 2*a^3*b  + 4*a^2*b^2 - 2*a*b^3+ b^2*a^2  - 2*a* b^3 + b ^4"
    by auto
  also have "... = a^4  - 2*a^3*b  - 2*a^3*b +  a^2*b^2 +  4*a^2*b^2 - 2*a*b^3- 2*a*b^3 +a^2*b^2 + b ^4 "
    by auto
  finally show ?thesis
    by auto
qed

lemma pomocna_1:
  fixes a b c d :: real
  assumes "a + b + c + d = 6" "a\<^sup>2 + b\<^sup>2 + c\<^sup>2 + d\<^sup>2 = 12"
  shows "4*(a^3 + b^3 + c^3 + d^3) - (a^4 + b^4 + c^4 + d^4) = -((a-1)^4 + (b-1)^4  + (c-1)^4 + (d-1)^4) + 52"
proof -
  have "4*(a^3 + b^3 + c^3 + d^3) - (a^4 + b^4 + c^4 + d^4) =
         4*a^3 + 4*b^3 + 4*c^3 + 4*d^3 - a ^4 - b ^4  - c ^4 - d ^4 "
    by auto
  also have "... = -( a ^4 + b ^4  + c ^4 + d ^4) +  4*a^3 + 4*b^3 + 4*c^3 + 4*d^3 "
    by auto
  also have
    "... = -((a-1) ^4 + 4*a^3 - 6*a^2 + 4*a -1 + b ^4  + c ^4 + d ^4) +  4*a^3 + 4*b^3 + 4*c^3 + 4*d^3 "
    by (auto simp add: razlika_na_4)
  also have "... = -((a-1) ^4 + b ^4  + c ^4 + d ^4) +  4*a^3  - 4*a^3 + 6*a^2 - 4*a +1 + 4*b^3 + 4*c^3 + 4*d^3 "
    by auto
  also have "... = -((a-1) ^4 + b ^4  + c ^4 + d ^4)  + 6*a^2 - 4*a +1 + 4*b^3 + 4*c^3 + 4*d^3 "
    by auto
  also have "... = -((a-1) ^4 + (b-1) ^4+ 4*b^3 - 6*b^2 + 4*b -1  + c ^4 + d ^4)  + 6*a^2 - 4*a +1 + 4*b^3 + 4*c^3 + 4*d^3 "
    by (auto simp add: razlika_na_4)
  also have "... = -((a-1) ^4 + (b-1) ^4  + c ^4 + d ^4)  + 6*a^2 - 4*a +1 + 4*b^3 - 4*b^3 + 6*b^2 - 4*b +1 + 4*c^3 + 4*d^3 "
    by auto
  also have "... = -((a-1) ^4 + (b-1) ^4  + c ^4 + d ^4)  + 6*a^2 - 4*a +1 + 6*b^2 - 4*b +1 + 4*c^3 + 4*d^3 "
    by auto
  also have "... = -((a-1)^4 + (b-1)^4  + (c-1)^4 + 4*c^3 - 6*c^2 + 4*c -1   + d ^4)  + 6*a^2 - 4*a +1 + 6*b^2 - 4*b +1 + 4*c^3 + 4*d^3"
    by (auto simp add: razlika_na_4)
  also have "... = -((a-1)^4 + (b-1)^4  + (c-1)^4 + d ^4)  + 6*a^2 - 4*a +1 + 6*b^2 - 4*b +1 + 4*c^3 - 4*c^3 + 6*c^2 - 4*c +1 + 4*d^3"
    by auto
  also have "... =-((a-1)^4 + (b-1)^4  + (c-1)^4 + d ^4)  + 6*a^2 - 4*a +1 + 6*b^2 - 4*b +1 + 6*c^2 - 4*c +1 + 4*d^3 "
    by auto
   also have "... = -((a-1)^4 + (b-1)^4  + (c-1)^4 + (d-1)^4 +  4*d^3 - 6*d^2 + 4*d -1)  + 6*a^2 - 4*a +1 + 6*b^2 - 4*b +1 + 6*c^2 - 4*c +1 + 4*d^3"
     by (auto simp add: razlika_na_4)
   also have "... = -((a-1)^4 + (b-1)^4  + (c-1)^4 + (d-1)^4) + 6*a^2 - 4*a +1 + 6*b^2 - 4*b +1 + 6*c^2 - 4*c +1 + 4*d^3 - 4*d^3 + 6*d^2 - 4*d +1"
     by auto
   also have "... = -((a-1)^4 + (b-1)^4  + (c-1)^4 + (d-1)^4) + 6*(a^2 + b^2 + c^2 + d ^ 2) - 4*(a + b + c +d) +4"
     by auto
   also have "... =  -((a-1)^4 + (b-1)^4  + (c-1)^4 + (d-1)^4) + 6 * 12 - 4 * 6 + 4"
     using assms
     by auto
   finally show ?thesis 
     by auto
     
 qed

lemma suma_na_kvadrat_svaki_jednako_4:
  fixes a b c d x y z t :: real
  assumes "a + b + c + d = 6" "a\<^sup>2 + b\<^sup>2 + c\<^sup>2 + d\<^sup>2 = 12"
          "x = a-1 \<and> y = b-1 \<and> z = c-1 \<and> t = d-1"
  shows"x^2 + y^2 + z^2 + t^2 = 4"
proof-
  have "x^2 + y^2 + z^2 + t^2 = (a-1)^2 + (b-1)^2 + (c-1)^2 + (d-1)^2"
    using assms(3)
    by auto
  also have "... = a^2 - 2*a + 1 + b^2 - 2*b + 1 + c^2 - 2*c + 1 + d^2 - 2*d + 1 "
    by (simp add: razlika_sa_1_na_2)
  also have "... = a^2 + b^2 + c^2 + d^2 - 2* (a + b + c + d) +4"
    by auto
  also have "... = 12 - 2*6 + 4"
    using assms(1) assms(2)
    by auto
  also have "... = 4"
    by auto
  finally show ?thesis
    .
qed

lemma suma_na_kvadrat_svaki_na_kvadrat:
  fixes x y z t :: real
  assumes "x^2 + y^2 + z^2 + t^2 = 4"
  shows"(x^2 + y^2 + z^2 + t^2)^2 = 16"
proof-
  have "(x^2 + y^2 + z^2 + t^2)^2 =(x^2 + y^2 + z^2 + t^2)* (x^2 + y^2 + z^2 + t^2) "
    by (auto simp add: power2_eq_square)
  also have "... = 16"
    using assms
    by auto
  finally show ?thesis
    .
qed



lemma vece_od_nula:
 fixes a b c d :: real
 assumes "a^2 + b^2 + c^2 + d^2 = 4"
         " a + b + c + d = 2"
       shows "0 \<le> 2*(a^2*b^2 + a^2*c^2 + a^2*d^2 + b^2*c^2 + b^2*d^2 + c^2*d^2)"
  by simp




lemma pomocna_3:
  fixes x y z t :: real
  shows "(x^2 + y^2 + z^2 + t^2)^2 = x^4 + y^4 + z^4 + t^4 + 2*(x^2*y^2 + x^2*z^2 + x^2*t^2 + y^2*z^2 + y^2*t^2 + z^2*t^2)"
proof-
  have "(x^2 + y^2 + z^2 + t^2) ^ 2 =  (x^2 + y^2 + z^2 + t^2) * (x^2 + y^2 + z^2 + t^2)"
    by (simp add: power2_eq_square)
  also have "... = x^2*x^2 + x^2*y^2 + x^2*z^2 + x^2*t^2 + y^2*x^2 + y^2*y^2 + y^2*z^2 + y^2*t^2 +  z^2*x^2 + z^2*y^2 + z^2*z^2 + z^2*t^2 +  t^2*x^2 + t^2*y^2 + t^2*z^2 + t^2*t^2  "
    by (auto simp add: algebra_simps)
  also have "\<dots> =x^4 + y^4 + z^4 + t^4 + 2*(x^2*y^2 + x^2*z^2 + x^2*t^2 + y^2*z^2 + y^2*t^2 + z^2*t^2) "
    by (auto simp add: algebra_simps)
  then show ?thesis
    using calculation by presburger
qed


lemma pomocna_2:
  fixes x y z t :: real
  assumes "x^2 + y^2 + z^2 + t^2 = 4"
           "x + y + z + t = 2"
  shows " x^4 + y^4 + z^4 + t^4  \<le> (x^2 + y^2 + z^2 + t^2)^2 "
proof-
  have "(x^2 + y^2 + z^2 + t^2)^2 =  x^4 + y^4 + z^4 + t^4 + 2*(x^2*y^2 + x^2*z^2 + x^2*t^2 + y^2*z^2 + y^2*t^2 + z^2*t^2)"
    by (auto simp add: pomocna_3)
  have "x^4 + y^4 + z^4 + t^4 \<le> x^4 + y^4 + z^4 + t^4 + 2*(x^2*y^2 + x^2*z^2 + x^2*t^2 + y^2*z^2 + y^2*t^2 + z^2*t^2)"
   by simp
  then show ?thesis
    by (auto simp add: pomocna_3)
qed

lemma power_mean:
  fixes x y z t :: real
  shows "((x^2 + y^2 + z^2 + t^2)/4)^2*4  \<le> (x^4 + y^4 + z^4 + t^4)"
  sorry

lemma pomocna_drugi_deo:
  fixes x y z t :: real 
  shows "((x^2 + y^2 + z^2 + t^2)/4)^2*4 = ((x^2 + y^2 + z^2 + t^2)^2)/4"
proof-
  have "((x^2 + y^2 + z^2 + t^2)/4)^2*4 =((x^2 + y^2 + z^2 + t^2)^2/(4*4))*4 "
    by (simp add: power2_eq_square)
  also have "\<dots> = ((x^2 + y^2 + z^2 + t^2)^2/16)*4"
    by auto
  also have "\<dots> = ((x^2 + y^2 + z^2 + t^2)^2)/4"
    by auto
  finally show ?thesis
    .
qed

lemma glavna:
  fixes a b c d  :: real
  assumes "a + b + c + d = 6" "a\<^sup>2 + b\<^sup>2 + c\<^sup>2 + d\<^sup>2 = 12" 
         (* "x=a-1 \<and> y = b-1 \<and> z = c-1 \<and> t = d-1"*)
  shows "36 \<le> 4*(a^3 + b^3 + c^3 + d^3) - (a^4 + b^4 + c^4 + d^4)"
        " 4*(a^3 + b^3 + c^3 + d^3) - (a^4 + b^4 + c^4 + d^4) \<le> 48"
proof-
  show " 36 \<le> 4*(a^3 + b^3 + c^3 + d^3) - (a^4 + b^4 + c^4 + d^4)"
  proof- 
   have p1: "4*(a^3 + b^3 + c^3 + d^3) - (a^4 + b^4 + c^4 + d^4) = -((a-1)^4 + (b-1)^4  + (c-1)^4 + (d-1)^4) + 52"
      using assms pomocna_1
      by auto
    let ?x = "a-1" and ?y = "b-1" and ?z = "c-1" and ?t = "d-1"
    (*then  have "let x = (a-1); y=(b-1); z=(c-1); t=(d-1) in 4*(a^3 + b^3 + c^3 + d^3) - (a^4 + b^4 + c^4 + d^4) = -((a-1)^4 + (b-1)^4  + (c-1)^4 + (d-1)^4) + 52"
      by auto *)
    have " ?x^4 +?y^4 + ?z^4 + ?t^4 \<le> (?x^2 + ?y^2 + ?z^2 + ?t^2)^2  "
      by (auto simp add: pomocna_3)
    then have p2: "?x^4 + ?y^4 + ?z^4 + ?t^4 \<le> 16"
      using assms
      by (auto simp add: suma_na_kvadrat_svaki_jednako_4)
    have p3:"4*(a^3 + b^3 + c^3 + d^3) - (a^4 + b^4 + c^4 + d^4) = -(?x^4 + ?y^4 + ?z^4 + ?t^4) + 52"
      using assms p1 p2
      by auto
    have " -16 + 52 \<le>4*(a^3 + b^3 + c^3 + d^3) - (a^4 + b^4 + c^4 + d^4)"
      using  p2 p3
      by auto
    then have "36 \<le> 4*(a^3 + b^3 + c^3 + d^3) - (a^4 + b^4 + c^4 + d^4)"
      by auto
    then show ?thesis
      .
    qed
  next
  show "4*(a^3 + b^3 + c^3 + d^3) - (a^4 + b^4 + c^4 + d^4) \<le> 48"
  proof -
     have p1: "4*(a^3 + b^3 + c^3 + d^3) - (a^4 + b^4 + c^4 + d^4) = -((a-1)^4 + (b-1)^4  + (c-1)^4 + (d-1)^4) + 52"
      using assms pomocna_1
      by auto
    let ?x = "a-1" and ?y = "b-1" and ?z = "c-1" and ?t = "d-1"
    have "((?x^2 + ?y^2 + ?z^2 + ?t^2)/4)^2*4  \<le> (?x^4 + ?y^4 + ?z^4 + ?t^4)"
      by (simp add: power_mean)
    then have p3:"((?x^2 + ?y^2 + ?z^2 + ?t^2)^2)/4 \<le>  (?x^4 + ?y^4 + ?z^4 + ?t^4)"
      by (simp add: pomocna_drugi_deo)
    have p4: "?x^2 + ?y^2 + ?z^2 + ?t^2 = 4"
      using assms
      by (meson suma_na_kvadrat_svaki_jednako_4)
    have "16 /4 \<le>  (?x^4 + ?y^4 + ?z^4 + ?t^4)"
      using p3 p4
      by (simp add: suma_na_kvadrat_svaki_na_kvadrat)
    then have "4 \<le>  (?x^4 + ?y^4 + ?z^4 + ?t^4)"
      by auto
    then have "4 \<le>  (a-1)^4 + (b-1)^4 + (c-1)^4 + (d-1)^4"
      by auto
    then have " -((a-1)^4 + (b-1)^4  + (c-1)^4 + (d-1)^4) \<le> -4"
      by auto
    then have " -((a-1)^4 + (b-1)^4  + (c-1)^4 + (d-1)^4) + 52 \<le> -4+52"
      by auto
    then have "-((a-1)^4 + (b-1)^4  + (c-1)^4 + (d-1)^4) + 52 \<le> 48" 
      by auto
    then have "4*(a^3 + b^3 + c^3 + d^3) - (a^4 + b^4 + c^4 + d^4) \<le> 48"
      using p1
      by auto
    then show ?thesis
      .
  qed
 qed

