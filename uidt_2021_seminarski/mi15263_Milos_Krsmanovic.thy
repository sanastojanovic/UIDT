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

(* 

Kosi-Svarcova nejednakost
(a1^2 + a2^2 + ... + an^2)*(b1^2 + b2^2 + ... + bn^2) \<ge> (a1*b1 + a2*b2 * ... * an*bn)^2

Za ovaj zadatak umesto opsteg slucaja, koristicemo slucaj n=3

(a1^2 + a2^2 + a3^2)*(b1^2 + b2^2 + b3^2) \<ge> (a1*b1 + a2*b2 * a3*b3)^2
   (prvi_clan_KS)       (drugi_clan_KS)       (desna_strana_KS)
*)

lemma kosi_svarc:
  fixes a1 a2 a3 b1 b2 b3 :: real
  assumes "a1 > 0" "a2 > 0" "a3 > 0" "b1 > 0" "b2 > 0" "b3 > 0"
  shows "(a1^2 + a2^2 + a3^2)*(b1^2 + b2^2 + b3^2) \<ge> (a1*b1 + a2*b2 * a3*b3)^2"
  sorry

(*I finalnu nejednakost  potrebno je rasclaniti na faktore koji se potom zasebno transformisu:*)
lemma prvi_clan_KS[simp]:
  fixes a1 a2 a3 x y z :: real
  assumes "a1 > 0" "a2 > 0" "a3 > 0" "x > 0" "y > 0" "z > 0"
  assumes "a1 = sqrt(y + z)" "a2 = sqrt(z + x)" "a3 = sqrt(x + y)"
  shows "(a1^2 + a2^2 + a3^2) = 2*(x + y + z)"
proof -
  have "a1^2 = y + z" and  "a2^2 = z + x" and "a3^2 = x + y"
    using assms
    by auto
  also have "(a1^2 + a2^2 + a3^2) = (y + z + z + x + x + y)"
    by (simp add: calculation(1) calculation(2) calculation(3))
  have "... = (2*x + 2*y + 2*z)"
    by simp
  have "... = 2*(x + y + z)"
    by simp
  then show ?thesis
    using assms
    by simp
qed


lemma drugi_clan_KS[simp]:
  fixes a1 a2 a3 b1 b2 b3 x y z :: real
  assumes "x > 0" "y > 0" "z > 0"
  assumes "a1 > 0" "a2 > 0" "a3 > 0"
  assumes "a1 = sqrt(y + z)" "a2 = sqrt(z + x)" "a3 = sqrt(x + y)"
  (*Uvodjenje pogodne smene*)
  assumes "b1 > 0" "b2 > 0" "b3 > 0"
  assumes "b1 = x/a1" "b2 = y/a2" "b3 = z/a3"
  shows "(b1^2 + b2^2 + b3^2) = (x^2/(y + z) + y^2/(z + x) + z^2/(x + y))"
proof - 
  have "(b1^2 + b2^2 + b3^2) = ((x/sqrt(y + z))^2 + (y/sqrt(z + x))^2 + (z/sqrt(x + y))^2)"
    using assms(7) assms(8) assms(9) assms(13) assms(14) assms(15)
    by simp
  also have "... = (x^2/(sqrt(y + z))^2 + y^2/(sqrt(z + x))^2 + z^2/(sqrt(x + y))^2)"
    using assms
    by (simp add: power_divide)
  then have "... = (x^2/(y + z) + y^2/(z + x) + z^2/(x + y))"
    using assms
    by simp
  then show ?thesis
    using assms
    by (simp add: \<open>(x / sqrt (y + z))\<^sup>2 + (y / sqrt (z + x))\<^sup>2 + (z / sqrt (x + y))\<^sup>2 = x\<^sup>2 / (sqrt (y + z))\<^sup>2 + y\<^sup>2 / (sqrt (z + x))\<^sup>2 + z\<^sup>2 / (sqrt (x + y))\<^sup>2\<close>)
qed

(*koristeci iste smene, dokazujemo ispravnost desne strane nejednakosti*)
lemma desna_strana_KS[simp]:
  fixes a1 a2 a3 b1 b2 b3 x y z :: real
  assumes "x > 0" "y > 0" "z > 0"
  assumes "a1 > 0" "a2 > 0" "a3 > 0" "b1 > 0" "b2 > 0" "b3 > 0"
  assumes "a1 = sqrt(y + z)" "a2 = sqrt(z + x)" "a3 = sqrt(x + y)"
  assumes "b1 = x/a1" "b2 = y/a2" "b3 = z/a3"
  shows "(a1*b1 + a2*b2 + a3*b3) = (x + y + z)"
proof -
  have "(a1*b1 + a2*b2 + a3*b3) = (a1 * x/a1 + a2 * y/a2 + a3 * z/a3)"
    by (simp add: assms(13) assms(14) assms(15))
  then have "... = (x + y + z)"
    using assms(4) assms(5) assms(6) 
    by auto
  then show ?thesis
    by (simp add: \<open>a1 * b1 + a2 * b2 + a3 * b3 = a1 * x / a1 + a2 * y / a2 + a3 * z / a3\<close>)
qed


(*Nejednakost koju cine dokazani clanovi potrebno je objediniti i preforumulisati*)

lemma objedinjena_KS:
  fixes a1 a2 a3 b1 b2 b3 x y z :: real
  assumes "\<forall> x y z :: real. x > 0 \<and> y > 0  \<and> z > 0"
  assumes "\<forall> a1 a2 a3 :: real. a1 > 0 \<and> a2 > 0 \<and> a3 > 0" 
  assumes "\<forall> b1 b2 b3 :: real. b1 > 0 \<and> b2 > 0 \<and> b3 > 0"
  assumes "a1 = sqrt(y + z)" "a2 = sqrt(z + x)" "a3 = sqrt(x + y)"
  assumes "b1 = x/a1" "b2 = y/a2" "b3 = z/a3"
  shows "(a1^2 + a2^2 + a3^2)*(b1^2 + b2^2 + b3^2) \<ge> (a1*b1 + a2*b2 * a3*b3)^2  \<longleftrightarrow> 
         2*(x + y + z)*(x^2/(y + z) + y^2/(z + x) + z^2/(x + y)) \<ge> (x + y + z)^2"
proof-
  show ?thesis
    using assms
    by auto
qed

lemma preformulisana_nejednakost:
  fixes x y z :: real
  assumes "\<forall> x y z :: real. x > 0 \<and> y > 0  \<and> z > 0"
  shows "2*(x + y + z)*(x^2/(y + z) + y^2/(z + x) + z^2/(x + y)) \<ge> (x + y + z)^2  \<longleftrightarrow> 
         (x^2/(y + z) + y^2/(z + x) + z^2/(x + y)) \<ge> (1/2) * (x + y + z)"
proof - 
  have "2*(x + y + z)*(x^2/(y + z) + y^2/(z + x) + z^2/(x + y)) \<ge> (x + y + z)^2  \<longleftrightarrow>
       2*(x + y + z)*(x^2/(y + z) + y^2/(z + x) + z^2/(x + y)) \<ge> (x + y + z)*(x + y + z)"
    using assms
    by auto
  also have "... \<longleftrightarrow> 2*(x^2/(y + z) + y^2/(z + x) + z^2/(x + y)) \<ge> (x + y + z)"
    using assms
    by auto
  also have "... \<longleftrightarrow> (x^2/(y + z) + y^2/(z + x) + z^2/(x + y)) \<ge> (x + y + z)/2"
    using assms
    by auto
  then have "... \<longleftrightarrow> (x^2/(y + z) + y^2/(z + x) + z^2/(x + y)) \<ge> (1/2) * (x + y + z)"
    using assms
    by simp
  then show ?thesis
    using assms
    by smt
qed

(*
  Ovim je pokazano da je nejednakost (dobijena korektnim uvodjenjem smena u polaznu) 
  
  (x^2/(y + z) + y^2/(z + x) + z^2/(x + y)) \<ge> (1/2) * (x + y + z)
 
  a kako je, nejednakoscu aritmeticke i geomtrijske sredine, dokazano da je (x + y + z) \<ge> 3 
  to se onda moze preneti i na navedenu nejednakost te ce ona biti:
  
  (x^2/(y + z) + y^2/(z + x) + z^2/(x + y)) \<ge> (3/2)
  
  sto je pokazano u narednoj (finalnoj) lemi.
*)

lemma konacna_nejedankost:
  fixes x y z :: real
  assumes "\<forall> x y z :: real. x > 0 \<and> y > 0  \<and> z > 0"
  shows "(x^2/(y + z) + y^2/(z + x) + z^2/(x + y)) \<ge> (3/2)"
proof -
  have "(x^2/(y + z) + y^2/(z + x) + z^2/(x + y)) \<ge> (1/2) * (x + y + z)"
    using assms preformulisana_nejednakost
    by blast
  also have "... \<ge> (1/2) * 3"
    using assms zbir_ge_3
    by blast
  then have "... \<ge> (3/2)"
    using assms
    by blast
  then show ?thesis
    using assms
    by auto
qed

end