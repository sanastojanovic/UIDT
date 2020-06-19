(*
Naslov: Prvi seminarski zadatak
Autor: Anđelka Milovanović, mi15145
*)

theory mi15145_Andelka_Milovanovic
  imports Complex_Main
begin

section "Seminarski 1"
text 
  \<open> 
    Dan 2, zadatak 2 na linku: https://imomath.com/srb/zadaci/BIH_2011_bihmo_resenja.pdf
    
    Neka su a, b i c pozitivni realni brojevi čiji je zbir jednak 1. Dokazati da vrijedi 
    nejednakost:
      a * (1 + b - c) ^ (1/3) + b * (1 + c - a) ^ (1/3) + c * (1 + a - b) ^ (1/3) \<le> 1.
  \<close>

(* sa interneta provera za powr i root
thm powr_def
thm root_def

lemma root_powr_inverse:
  "0 < n ==> 0 < x ==> root n x = x powr (1/n)"
  using root_powr_inverse by blast
*)

text
  \<open>
    Pokazujemo da su 1+b-c, 1+c-a, 1+a-b pozitivni realni brojevi
  \<close>
lemma pozitivno_1_plus_b_minus_c:
  fixes a b c :: real
  assumes "a > 0" "b > 0" "c > 0" "a + b + c = 1" 
  shows "1 + b - c > 0"
  sorry
(*
  using assms
  by linarith
*)

lemma pozitivno_1_plus_c_minus_a:
  fixes a b c :: real
  assumes "a > 0" "b > 0" "c > 0" "a + b + c = 1" 
  shows "1 + c - a > 0"
  sorry
(*
  using assms
  by linarith
*)

lemma pozitivno_1_plus_a_minus_b:
  fixes a b c :: real
  assumes "a > 0" "b > 0" "c > 0" "a + b + c = 1" 
  shows "1 + a - b > 0"
  sorry
(*
  using assms
  by linarith
*)

lemma nejednakost_aritmeticka_geometrijska_2:
  assumes "x > 0" "y > 0"
  shows "(x + y) / 2 \<ge> root 2 (x * y)"
  using assms arith_geo_mean_sqrt sqrt_def 
  by auto

text
  \<open>
    Na osnovu AG nejednakosti imaćemo da su: 
        (1+1+(1+b-c)/3)\<ge>root 3 (1+b-c)
        (1+1+(1+c-a)/3)\<ge>root 3 (1+c-a)
        (1+1+(1+a-b)/3)\<ge>root 3 (1+a-b) 
  \<close>

lemma nejednakost_aritmeticka_geometrijska_3:
  assumes "x > 0" "y > 0" "z > 0"
  shows "root 3 (x * y * z) \<le> (x + y + z) / 3"
  sorry

(* root 3 (1+b-c) \<le> (1+1+(1+b-c))/3 = 1 + (b-c)/3 *)
lemma pomocna_lema_nejednakosti:
  fixes a b c :: real
  assumes "a > 0" "b > 0" "c > 0" "a + b + c = 1"
  shows "root 3 (1 + b - c) \<le> 1 + (b - c) / 3"
  sorry

(*
proof-
  have "root 3 (1 + b - c) = root 3 (1 * 1 * (1 + b - c))"
    by simp
  also have "... \<le> (1 + 1 + (1 + b - c)) / 3"
    using assms
    by (smt nejednakost_aritmeticka_geometrijska_3 power2_eq_square power_one)
  also have "... = 1 + (b - c) / 3"
    by simp
  finally show ?thesis
    .
qed
*)

(* a * root 3 (1+b-c) \<le> a + (a * b - a * c)/3 *)
lemma prvi_clan_izraza [simp]:
  fixes a b c :: real
  assumes "a > 0" "b > 0" "c > 0" "a + b + c = 1"
  shows "a * root 3 (1 + b - c) \<le> a + (a*b - a*c) / 3"
  sorry
(*
proof-
  have "a * root 3 (1 + b - c) \<le> a * (1 + (b - c) / 3)"
    using pomocna_lema_nejednakosti assms
    by simp
  also have "... = a + a * (b - c) / 3"
    by (metis (no_types, hide_lams)  add_diff_cancel cancel_comm_monoid_add_class.diff_cancel 
        diff_diff_eq2 mult.right_neutral  right_diff_distrib' times_divide_eq_right)
  also have "... = a + (a*b - a*c) / 3"
    by (simp add: right_diff_distrib')
  finally show ?thesis
    .
qed
*)

(* b * root 3 (1+c-a) \<le> b + (b * c - b * a)/3 *)
lemma drugi_clan_izraza [simp]:
  fixes a b c :: real
  assumes "a > 0" "b > 0" "c > 0" "a + b + c = 1"
  shows "b * root 3 (1 + c - a) \<le> b + (b*c - b*a) / 3"
  sorry

(* c * root 3 (1+a-b) \<le> c + (c * a - c * b)/3 *)
lemma treci_clan_izraza [simp]:
  fixes a b c :: real
  assumes "a > 0" "b > 0" "c > 0" "a + b + c = 1"
  shows "c * root 3 (1 + a - b) \<le> c + (c*a - c*b) / 3"
  sorry


text 
  \<open>
    Pokazujemo konačno tvrđenje zadatka na osnovu prethodnih lema
  \<close>

lemma a_b_c_izraz:
  fixes a b c :: real
  assumes "a > 0" "b > 0" "c > 0" "a + b + c = 1"
  shows " a + b + c + (a*b - a*c)/3 + (b*c - b*a) / 3 + (c*a - c*b) / 3 =  a + b + c"
  sorry
(*
proof-
  have " a + b + c + (a*b - a*c)/3 + (b*c - b*a) / 3 + (c*a - c*b) / 3 = 
         a + b + c + (a*b)/3 - (a*c)/3 + (b*c - b*a) / 3 + (c*a - c*b) / 3"
    by auto
  also have "... =  a + b + c + (a*b)/3 - (a*c)/3 + (b*c)/3 - (b*a)/3 + (c*a - c*b) / 3"
    by (simp add: diff_divide_distrib)
  also have "... =  a + b + c + (a*b)/3 - (a*c)/3 + (b*c)/3 - (b*a)/3 + (c*a)/3 - (c*b)/3"
    by (smt add_divide_distrib)
  also have "... =  a + b + c + (a*b)/3 - (a*b)/3 - (a*c)/3 + (a*c)/3 + (b*c)/3 - (b*c)/3"
    by auto
  also have "... =  a + b + c"
    by auto
  finally show ?thesis
    .
qed
*)
lemma zadatak:
  fixes a b c :: real
  assumes "a > 0" "b > 0" "c > 0" "a + b + c = 1"
  shows "a * root 3 (1 + b - c) + b * root 3 (1 + c - a) + c * root 3 (1 + a - b) \<le> 1"
  sorry
(*
proof-
  have "a * root 3 (1 + b - c) + b * root 3 (1 + c - a) + c * root 3 (1 + a - b) \<le> 
        a + (a*b - a*c) / 3 + b * root 3 (1 + c - a) + c * root 3 (1 + a - b)"
    using assms
    by auto
  also have "... \<le>  a + (a*b - a*c) / 3 +  b + (b*c - b*a) / 3 + c * root 3 (1 + a - b)"
    using assms
    by auto
  also have "... \<le>  a + (a*b - a*c) / 3 +  b + (b*c - b*a) / 3 + c + (c*a - c*b) / 3"
    using assms
    by auto
  also have "... = a + b + c + (a*b-a*c)/3 + (b*c - b*a) / 3 + (c*a - c*b) / 3"
    by simp
  also have "... = a + b + c"
    using a_b_c_izraz assms
    by blast
  also have "... = 1"
    by (simp add: assms(4))
  finally show ?thesis
    .
qed
*)
end