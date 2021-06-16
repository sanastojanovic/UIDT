(* 
  I \<and> II Seminarski u okviru kursa Uvod u interaktivno dokazivanje teorema
  Profesor: dr Filip Maric
  Asistent: dr Sana Stojanovic Djurdjevic
  Student:  Milos Krsmanovic, mi15263
*)
theory mi15263_Milos_Krsmanovic
  imports Complex_Main "HOL-Library.Multiset"
begin

text\<open>
  Medjunarodna matematicka olimpijada 1995. god.

  Problem 2:
  Neka su a, b i c pozitivni realni brojevi, takvi da je 
  a * b * c = 1. Dokazati da vazi naredno tvrdjenje:

   1/(a^3*(b + c)) + 1/(b^3*(c + a)) + 1/(c^3*(a + b)) \<ge> 3/2
\<close>
(* Prvi seminarski: formulacija problema*)

fun glavna_nejednakost :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
"glavna_nejednakost a b c = 1/(a^3*(b + c)) + 1/(b^3*(c + a)) + 1/(c^3*(a + b))"

value "glavna_nejednakost 1 1 1"
value "glavna_nejednakost (1/5) (1/5) (1/2)"


lemma nejednakost: 
  fixes a b c :: real
  assumes "a * b * c = 1"
  shows "1 / (a^3 * (b + c)) + 
         1 / (b^3 * (c + a)) + 
         1 / (c^3 * (a + b)) \<ge> 3/2"
  sorry

(* Drugi seminarski: raspisivanje dokaza*)

lemma metod_smene:
  fixes a b c x y z :: real
  assumes "x=1/a" "y=1/b" "z=1/c"
  shows "1 / (a^3 * (b + c)) + 
         1 / (b^3 * (c + a)) + 
         1 / (c^3 * (a + b)) = 
         x^3/(x * y * z * (1/y + 1/z)) + 
         y^3/(x * y * z * (1/z + 1/x)) + 
         z^3/(x * y * z * (1/x + 1/y))"
  sorry  
(*using assms
  by blast*)

lemma metod_smene_2:
  fixes a b c x y z :: real
  assumes "1 / (a^3 * (b + c)) + 
         1 / (b^3 * (c + a)) + 
         1 / (c^3 * (a + b)) = 
         x^3/(x * y * z * (1/y + 1/z)) + 
         y^3/(x * y * z * (1/z + 1/x)) + 
         z^3/(x * y * z * (1/x + 1/y))"
  shows "x^3/(x * y * z * (1/y + 1/z)) + 
         y^3/(x * y * z * (1/z + 1/x)) + 
         z^3/(x * y * z * (1/x + 1/y)) =
         x^2/(y + z) + y^2/(z + x) + z^2/(x + y)"
  sorry

(*Pomocne leme za glavnu nejednakost*)
lemma amgm:
  fixes x y z :: real
  assumes "x>0" "y>0" "z>0" "x\<le>1" "y\<le>1" "z\<le>1"
  assumes "x * y * z = 1"
  shows "(x + y + z)/3 \<ge> root 3 (x * y * z)"
  thm arith_geo_mean_sqrt
  using arith_geo_mean_sqrt assms
  by blast

lemma pomocna_1_1:
  fixes x y z :: real
  assumes "x>0 \<and> y>0 \<and> z>0"
  shows "z/(y*z) + y/(y*z) = (z+y)/(y*z)"
  using assms
  by (simp add: add_divide_distrib)

(*--------prvi deo glavne nejednakosti-----------------*)

lemma prvi_deo[simp]:
  fixes x y z :: real
  assumes "x>0 \<and> y>0 \<and> z>0 \<and> x*y*z=1"
  shows "1/((1/x)^3*(1/y + 1/z)) = x^2/(y + z)"
proof-
  have "1/((1/x)^3*(1/y + 1/z)) = x^3/(1/y + 1/z)"
    by (simp add: assms power_one_over)
  then have "x^3/(1/y + 1/z) = x^3/(z/(y*z) + y/(y*z))"
    using assms
    by auto
  then have "x^3/(z/(y*z) + y/(y*z)) = x^3/((z+y)/(y*z))"
    by (metis assms pomocna_1_1)
  then have "x^3/((z+y)/(y*z)) = (x^3*y*z)/(z+y)"
    by simp
  then have "(x^3*y*z)/(z+y) = (x^2*x*y*z)/(z+y)"
    by (simp add: power2_eq_square power3_eq_cube)
  then have "(x^2*x*y*z)/(z+y) = x^2/(z+y)"
    using assms by auto
  then show ?thesis
    by (smt \<open>1 / ((1 / x) ^ 3 * (1 / y + 1 / z)) = x ^ 3 / (1 / y + 1 / z)\<close> \<open>x ^ 3 * y * z / (z + y) = x\<^sup>2 * x * y * z / (z + y)\<close> \<open>x ^ 3 / ((z + y) / (y * z)) = x ^ 3 * y * z / (z + y)\<close> \<open>x ^ 3 / (1 / y + 1 / z) = x ^ 3 / (z / (y * z) + y / (y * z))\<close> \<open>x ^ 3 / (z / (y * z) + y / (y * z)) = x ^ 3 / ((z + y) / (y * z))\<close>)
qed

(*--------drugi deo glavne nejednakosti-----------------*)

lemma pomocna_2_1:
  fixes x y z :: real
  assumes "x>0 \<and> y>0 \<and> z>0"
  shows "x/(z*x) + z/(z*x) = (x+z)/(z*x)"
  using assms
  by (simp add: add_divide_distrib)

lemma drugi_deo[simp]:
  fixes x y z :: real
  assumes "x>0 \<and> y>0 \<and> z>0 \<and> x*y*z=1"
  shows "1/((1/y)^3*(1/z + 1/x)) = y^2/(x + z)"
proof-
  have "1/((1/y)^3*(1/z + 1/x)) = y^3/(1/z + 1/x)"
    by (simp add: assms power_one_over)
  then have "y^3/(1/z + 1/x) = y^3/(x/(z*x) + z/(z*x))"
    using assms
    by auto
  then have "y^3/(x/(z*x) + z/(z*x)) = y^3/((x+z)/(z*x))"
    by (metis assms pomocna_2_1)
  then have "y^3/((x+z)/(z*x)) = (y^3*z*x)/(x+z)"
    by simp
  then have "(y^3*z*x)/(x+z) = (y^2*y*z*x)/(x+z)"
    by (simp add: power2_eq_square power3_eq_cube)
  then have "(y^2*x*y*z)/(x+z) = y^2/(x + z)"
    using assms by auto
  then show ?thesis
  by (metis (no_types, lifting) \<open>1 / ((1 / y) ^ 3 * (1 / z + 1 / x)) = y ^ 3 / (1 / z + 1 / x)\<close> \<open>y ^ 3 / ((x + z) / (z * x)) = y ^ 3 * z * x / (x + z)\<close> \<open>y ^ 3 / (1 / z + 1 / x) = y ^ 3 / (x / (z * x) + z / (z * x))\<close> \<open>y ^ 3 / (x / (z * x) + z / (z * x)) = y ^ 3 / ((x + z) / (z * x))\<close> mult.commute mult.left_commute power2_eq_square power3_eq_cube)
qed

end