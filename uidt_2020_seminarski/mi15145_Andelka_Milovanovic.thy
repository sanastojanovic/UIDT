(*
  Naslov: Seminarski zadaci
  Autor: Anđelka Milovanović, mi15145
*)

theory mi15145_Andelka_Milovanovic
  imports Complex_Main
begin

section "Seminarski 1 \<and> raspisivanje dokaza lema za Seminarski 2"
text 
  \<open> 
    Dan 2, zadatak 2 na linku: https://imomath.com/srb/zadaci/BIH_2011_bihmo_resenja.pdf
    
    Neka su a, b i c pozitivni realni brojevi čiji je zbir jednak 1. Dokazati da vrijedi 
    nejednakost:
      a * (1 + b - c) ^ (1/3) + b * (1 + c - a) ^ (1/3) + c * (1 + a - b) ^ (1/3) \<le> 1.
  \<close>

text
  \<open>
    Pokazujemo da su 1+b-c, 1+c-a, 1+a-b pozitivni realni brojevi
  \<close>
lemma pozitivno_1_plus_b_minus_c:
  fixes a b c :: real
  assumes "a > 0" "b > 0" "c > 0" "a + b + c = 1" 
  shows "1 + b - c > 0"
proof-
  have "1 + b - c = a + b + c + b - c"
    using assms(4)
    by simp
  also have "... = a + 2*b"
    by simp
  also have "... > 0"
    using assms(1) assms(2) assms(3)
    by simp
  finally show ?thesis
    .
qed

lemma pozitivno_1_plus_c_minus_a:
  fixes a b c :: real
  assumes "a > 0" "b > 0" "c > 0" "a + b + c = 1" 
  shows "1 + c - a > 0"
  using assms
  by linarith

lemma pozitivno_1_plus_a_minus_b:
  fixes a b c :: real
  assumes "a > 0" "b > 0" "c > 0" "a + b + c = 1" 
  shows "1 + a - b > 0"
  using assms
  by linarith

text
  \<open>
    Na osnovu AG nejednakosti imaćemo da su: 
        (1+1+(1+b-c)/3)\<ge>root 3 (1+b-c)
        (1+1+(1+c-a)/3)\<ge>root 3 (1+c-a)
        (1+1+(1+a-b)/3)\<ge>root 3 (1+a-b) 

    jer smo pokazali da su 1+b-c, 1+c-a i 1+a-b pozitivni realni brojevi
  \<close>

thm root_def
lemma nejednakost_aritmeticka_geometrijska_2:
  assumes "x > 0" "y > 0"
  shows "(x + y) / 2 \<ge> root 2 (x * y)"
  thm arith_geo_mean_sqrt
  using assms arith_geo_mean_sqrt sqrt_def 
  by auto

lemma kvadrat_binoma:
  fixes x y :: real
  assumes "x>0" "y>0"
  shows "(x-y)^2 = x^2 - 2*x*y + y^2"
proof-
  have "(x-y)^2 = (x-y)*(x-y)"
    using power2_eq_square 
    by auto
  also have "... = (x*x-x*y-y*x+y*y)"
    by (simp add: left_diff_distrib' right_diff_distrib')
  also have "... = x^2 - 2*x*y + y^2"
    by (simp add: power2_eq_square)
  finally show ?thesis
    .
qed

lemma pomocna_za_AG_nejednakost_1:
  fixes x y z :: real
  assumes "x > 0" "y > 0" "z > 0"
  shows "(x + y + z) * ( (x-y)^2 + (y-z)^2 + (z-x)^2) = 
        2 * (x powr 3 + y powr 3 + z powr 3 - 3 * x * y * z)"
proof-
  have "(x + y + z) * ( (x-y)^2 + (y-z)^2 + (z-x)^2) = 
        (x + y + z) * ( x^2 - 2*x*y + y^2 + y^2 - 2*y*z + z^2 + z^2 - 2*z*x + x^2)"
    by (simp add: assms kvadrat_binoma)
  also have "... = (x+y+z) * (2*x^2 + 2*y^2 + 2*z^2 - 2*x*y - 2*y*z - 2*z*x)"
    by simp
  also have "... = x*(2*x^2 + 2*y^2 + 2*z^2 - 2*x*y - 2*y*z - 2*z*x) + 
                   y*(2*x^2 + 2*y^2 + 2*z^2 - 2*x*y - 2*y*z - 2*z*x) + 
                   z*(2*x^2 + 2*y^2 + 2*z^2 - 2*x*y - 2*y*z - 2*z*x)"
    by (simp add: semiring_normalization_rules(1))
  also have "... = x*2*x^2 + x*2*y^2 + x*2*z^2 - x*2*x*y - x*2*y*z - x*2*z*x +
                   y*2*x^2 + y*2*y^2 + y*2*z^2 - y*2*x*y - y*2*y*z - y*2*z*x + 
                   z*2*x^2 + z*2*y^2 + z*2*z^2 - z*2*x*y - z*2*y*z - z*2*z*x"
    by (simp add: distrib_left mult.assoc power2_commute right_diff_distrib)
  also have "... = 2*(x powr 3) + 2*x*y^2 + 2*x*z^2 - 2*x^2*y - 2*x*y*z - 2*x^2*z +
                   2*x^2*y + 2*(y powr 3) + 2*y*z^2 - 2*x*y^2 - 2*y^2*z - 2*x*y*z + 
                   2*x^2*z + 2*y^2*z + 2*(z powr 3) - 2*x*y*z - 2*y*z^2 - 2*x*z^2"
    by (simp add: assms power2_eq_square power3_eq_cube)
  also have "... = 2 * (x powr 3 + y powr 3 + z powr 3 - x*y*z - x*y*z - x*y*z)"
    by auto
  finally show ?thesis
    by auto   
qed

lemma pomocna_za_AG_nejednakost_2:
  fixes x y z :: real
  assumes "x > 0" "y > 0" "z > 0"
  shows "1/2 * (x + y + z) * ( (x-y)^2 + (y-z)^2 + (z-x)^2) = 
        (x powr 3 + y powr 3 + z powr 3 - 3 * x * y * z)"
proof-
  have "1/2 *( (x + y + z) * ( (x-y)^2 + (y-z)^2 + (z-x)^2)) = 
        1/2 * (2 * (x powr 3 + y powr 3 + z powr 3 - 3 * x * y * z))"
    by (simp add: assms pomocna_za_AG_nejednakost_1)
  also have "... = (x powr 3 + y powr 3 + z powr 3 - 3 * x * y * z)"
    by simp
  finally show ?thesis
    by auto
qed

lemma aritmeticka_geometrijska_razlika:
  fixes x y z u v w :: real
  assumes "x > 0" "y > 0" "z > 0" "u = root 3 x" "v = root 3 y" "w = root 3 z"
          "u > 0" "v > 0" "w > 0"
  shows "(x + y + z) / 3 - root 3 (x * y * z) \<ge> 0" 
proof-
  have "(x + y + z) / 3 - root 3 (x * y * z) = (u powr 3 + v powr 3 + w powr 3) / 3 - (u * v * w)"
    using assms
   by (simp add: real_root_mult)
  also have "... = 1/3 * (u powr 3 + v powr 3 + w powr 3 - 3 * u * v * w)"
    by auto
  also have "... = 1/6 * (u + v + w) * ( (u-v)^2 + (v-w)^2 + (w-u)^2)"
    using pomocna_za_AG_nejednakost_2 assms
    by simp    
  also have "... \<ge> 0"
    using assms
    by auto
  finally show ?thesis
    .
qed

lemma ag_nejednakost_root3:
  fixes x y z :: real
  assumes "x > 0" "y > 0" "z > 0" 
  shows "root 3 (x * y * z) <= (x + y + z) / 3 "
  using assms aritmeticka_geometrijska_razlika
  by simp

(* root 3 (1+b-c) \<le> (1+1+(1+b-c))/3 = 1 + (b-c)/3 *)
lemma pomocna_lema_nejednakosti:
  fixes a b c :: real
  assumes "a > 0" "b > 0" "c > 0" "a + b + c = 1"
  shows "root 3 (1 + b - c) \<le> 1 + (b - c) / 3"
proof-
  have "root 3 (1 + b - c) = root 3 (1 * 1 * (1 + b - c))"
    by simp
  also have "... \<le> (1 + 1 + (1 + b - c)) / 3"
    using assms
    by (smt ag_nejednakost_root3 power2_eq_square power_one)
  also have "... = 1 + (b - c) / 3"
    by simp
  finally show ?thesis
    .
qed

(* a * root 3 (1+b-c) \<le> a + (a * b - a * c)/3 *)
lemma clan_izraza [simp]:
  fixes a b c :: real
  assumes "a > 0" "b > 0" "c > 0" "a + b + c = 1"
  shows "a * root 3 (1 + b - c) \<le> a + (a*b - a*c) / 3"
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
(* Isto moze na osnovu prethodne leme za ova dva clana izraza, što i koristimo ispod u dokazu *)
(* b * root 3 (1+c-a) \<le> b + (b * c - b * a)/3 *)
(* c * root 3 (1+a-b) \<le> c + (c * a - c * b)/3 *)

text 
  \<open>
    Pomoćna lema za izračunavanje podizraza
  \<close>

lemma a_b_c_izraz:
  fixes a b c :: real
  assumes "a > 0" "b > 0" "c > 0" "a + b + c = 1"
  shows " a + b + c + (a*b - a*c)/3 + (b*c - b*a) / 3 + (c*a - c*b) / 3 =  a + b + c"
proof-
  have " a + b + c + (a*b - a*c)/3 + (b*c - b*a) / 3 + (c*a - c*b) / 3 = 
         a + b + c + (a*b)/3 - (a*c)/3 + (b*c - b*a) / 3 + (c*a - c*b) / 3"
    by auto
  also have "... =  a + b + c + (a*b)/3 - (a*c)/3 + (b*c)/3 - (b*a)/3 + (c*a - c*b) / 3"
    thm diff_divide_distrib
    by (simp add: diff_divide_distrib)
  also have "... =  a + b + c + (a*b)/3 - (a*c)/3 + (b*c)/3 - (b*a)/3 + (c*a)/3 - (c*b)/3"
    thm add_divide_distrib
    by (smt add_divide_distrib)
  also have "... =  a + b + c + (a*b)/3 - (a*b)/3 - (a*c)/3 + (a*c)/3 + (b*c)/3 - (b*c)/3"
    by auto
  also have "... =  a + b + c"
    by auto
  finally show ?thesis
    .
qed

text
  \<open>
    Konačno rešavanje postavljenog zadatka koristeći činjenice dokazane prethodno
  \<close>

lemma resenje_zadatka:
  fixes a b c :: real
  assumes "a > 0" "b > 0" "c > 0" "a + b + c = 1"
  shows "a * root 3 (1 + b - c) + b * root 3 (1 + c - a) + c * root 3 (1 + a - b) \<le> 1"
proof-
  have "a * root 3 (1 + b - c) + b * root 3 (1 + c - a) + c * root 3 (1 + a - b) \<le> 
        a + (a*b - a*c) / 3 + b * root 3 (1 + c - a) + c * root 3 (1 + a - b)"
    using assms 
    by simp
  also have "... \<le>  a + (a*b - a*c) / 3 +  b + (b*c - b*a) / 3 + c * root 3 (1 + a - b)"
    using assms
    by simp
  also have "... \<le>  a + (a*b - a*c) / 3 +  b + (b*c - b*a) / 3 + c + (c*a - c*b) / 3"
    using assms 
    by simp
  also have "... = a + b + c + (a*b-a*c)/3 + (b*c - b*a) / 3 + (c*a - c*b) / 3"
    by simp
  also have "... = a + b + c"
    using a_b_c_izraz assms
    by simp
  also have "... = 1"
    by (simp add: assms(4))
  finally show ?thesis
    .
qed

end