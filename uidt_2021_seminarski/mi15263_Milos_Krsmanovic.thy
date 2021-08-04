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
(* Formulacija problema:*)

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

(* Raspisivanje dokaza:*)


(*Rastavljanje LS nejednakosti na sabirke*)

lemma saberi_razlomke[simp]:
  assumes "\<forall> a b :: real. a \<noteq> 0 \<and> b \<noteq> 0"
  shows "1/a + 1/b = (b + a)/(a * b)"
  using assms
  by blast
  
lemma prvi_sabirak:
  fixes x y z :: real
  assumes "\<forall> a b c :: real. a>0 \<and> b>0 \<and> c>0 \<and> a*b*c=1" (*fiksiram konstante koje su vece od nula, a
  time postizem i ispravno uvodjenje smene.*)
  assumes "x=1/a" "y=1/b" "z=1/c"
    shows "1/(a^3 * (b + c)) = x^2/(y + z)"
proof-
  have "1/(a^3*(b + c)) = 1/((1/x)^3 * (1/y + 1/z))"
    using assms
    by auto
  also have "... = 1/((1/x^3) * (1/y + 1/z))"
    by (simp add: power_one_over)
  also have "... = x^3/(1/y + 1/z)"
    by simp
  also have "... = x^3/((z + y)/(y * z))"
    using assms(1)
    by auto
  also have "... = (x^3 * y * z)/(z + y)" (*   x^3 = x^2 * x   *)
    by auto
  then have "... = (x^2 * x * y * z)/(z + y)" (*   x * y * z = 1, iz uslova  *)
    using assms(1) 
    by auto
  then show ?thesis
    using assms(1) 
    by auto
qed

lemma drugi_sabirak:
  fixes x y z :: real
  assumes "\<forall> a b c :: real. a>0 \<and> b>0 \<and> c>0 \<and> a*b*c=1"
  assumes "x=1/a" "y=1/b" "z=1/c"
    shows "1/(b^3 * (c + a)) = y^2/(x + z)"
proof-
  have "1/(b^3 * (c + a)) = 1/((1/y)^3 * (1/z + 1/x))"
    using assms
    by auto
  also have "... = 1/((1/y^3) * (1/z + 1/x))"
    by (simp add: power_one_over)
  also have "... = y^3/(1/z + 1/x)"
    by simp
  also have "... = y^3/((x + z)/(z * x))"
    using assms(1)
    by auto
  also have "... = (y^3 * z * x)/(x + z)"
    by auto
  then have "... = (y^2 * y * z * x)/(x + z)"
    using assms(1) 
    by auto
  then show ?thesis
    using assms(1) 
    by auto
qed

lemma treci_sabirak:
  fixes x y z :: real
  assumes "\<forall> a b c :: real. a>0 \<and> b>0 \<and> c>0 \<and> a*b*c=1"
  assumes "x=1/a" "y=1/b" "z=1/c"
    shows "1/(c^3 * (a + b)) = z^2/(y + x)"
proof-
  have "1/(c^3 * (a + b)) = 1/((1/z)^3 * (1/x + 1/y))"
    using assms
    by auto
  also have "... = 1/((1/z^3)*(1/x + 1/y))"
    by (simp add: power_one_over)
  also have "... = z^3/(1/x + 1/y)"
    by simp
  also have "... = z^3/((y + x)/(x * y))"
    using assms(1)
    by auto
  also have "... = (z^3 * x * y)/(y + x)"
    by auto
  then have "... = (z^2 * z * x * y)/(y + x)"
    using assms(1) 
    by auto
  then show ?thesis
    using assms(1) 
    by auto
qed

lemma transformacija_polazne_nejednakosti:
  fixes x y z a b c :: real 
  assumes "\<forall> a b c :: real. a>0 \<and> b>0 \<and> c>0 \<and> a*b*c=1"
  assumes "\<forall> x y z :: real. x=1/a \<and> y=1/b \<and> z=1/c \<and> x*y*z=1"
  (*
    Uslov i dalje vazi: ako je   a    *    b    *     c  = 1 , to je 
                                1/x   *   1/y   *    1/z = 1 , to je dalje:
                                 x    *    y    *     z  = 1
  *)
  shows "1/(a^3 * (b + c)) + 
         1/(b^3 * (c + a)) + 
         1/(c^3 * (a + b)) = x^2/(y + z) + y^2/(z + x) + z^2/(x + y)"
  using prvi_sabirak drugi_sabirak treci_sabirak
  using assms(1)
  by auto


(* Nejednakost aritmeticke i geom. sredine, za n=3
   (x + y + z)/3 \<ge> root 3 x*y*z 
*)
lemma ag_mean:
  fixes x y z :: real
  assumes "x \<ge> 0" "y \<ge> 0" "z \<ge> 0"  "\<alpha> = (x + y + z) / 3" "y > \<alpha>" "z < \<alpha>" 
  shows "\<alpha> ^ 3 \<ge> x * y * z"
proof-
  have "\<alpha> \<ge> 0"
    using assms
    by simp
  have *: "(y - \<alpha>) * (\<alpha> - z) > 0"
    using assms
    by simp
  let ?y = "y + z - \<alpha>"
  have "?y > 0"
    using assms
    by simp
  have "3 * \<alpha> = (x + y + z)"
    using assms
    by simp
  then have "2 * \<alpha> = (x + ?y)"
    by simp
  then have "\<alpha> = (x + ?y) / 2"
    by simp
  then have "\<alpha> \<ge> sqrt (x * ?y)"
    using arith_geo_mean_sqrt[OF `x \<ge> 0`, of ?y] `?y > 0`
    by simp
  then have "\<alpha> ^ 2 \<ge> x * ?y"
    by (simp add: sqrt_le_D)
  then have **: "\<alpha> ^ 3 \<ge> x * ?y * \<alpha>"
    using `\<alpha> \<ge> 0`
    by (simp add: mult.commute mult_left_mono power2_eq_square power3_eq_cube)

  have "?y * \<alpha> - y * z = (y - \<alpha>)*(\<alpha> - z)"
    by (simp add: field_simps)
  then have "?y * \<alpha> - y * z  > 0"
    using *
    by simp
  then have ***: "?y * \<alpha> > y * z"
    by simp

  then have "x * (y * z) \<le> x * (?y * \<alpha>)"
    using `x \<ge> 0`
    using mult_le_cancel_left by fastforce
  then have "x * y * z \<le> x * ?y * \<alpha>"
    by simp
  then show ?thesis
    using **
    by simp
qed

(* Dokaz da je x + y + z \<ge> 3 *)

lemma zbir_ge_3:
  fixes x y z :: real
  assumes "\<forall> x y z :: real. x * y * z = 1" (*pokazano u prethodnoj lemi*)
  shows "(x + y + z) \<ge> 3"
proof -
  have "((x + y + z)/3 )^3 \<ge> x * y * z"
    by (smt assms mult_minus_right)
  then show ?thesis
    by (smt assms mult_minus_right)
qed

end