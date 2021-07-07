theory mi17259_Lazar_Celikovic
  imports Main Complex_Main HOL.Set "HOL-Library.Infinite_Set"
begin

text \<open>

link: https://imomath.com/srb/zadaci/2008_mmo.pdf
Algebra, zadatak 2

(a) Dokazati da je
    x^2 / (x - 1)^2 + y^2 / (y - 1)^2 + z^2 / (z - 1)^2 \<ge> 1
    za sve realne brojeve x, y i z takve da je svaki od njih
    razlicit od 1 i da vazi x*y*z = 1

(b) Dokazati da se jednakost dostize za beskonacno mnogo trojki
    racionalnih brojeva x, y i z za koje vazi da je svaka
    koordinata razlicita od 1 i da je proizvod 

\<close>

text \<open> Prvi deo seminarskog\<close>

lemma deo_pod_a:
  fixes x y z :: "real"
  assumes "x \<noteq> 1" "y \<noteq> 1" "z \<noteq> 1" "x * y * z = 1"
  shows "(x^2 / (x - 1)^2) + 
         (y^2 / (y - 1)^2) + 
         (z^2 / (z - 1)^2) \<ge> 1"
  using assms
  sorry

definition jedno_resenje :: "rat \<Rightarrow> rat \<Rightarrow> rat \<Rightarrow> bool" where
"jedno_resenje x y z = (x \<noteq> 1 \<and> 
                        y \<noteq> 1 \<and> 
                        z \<noteq> 1 \<and> 
                        x * y * z = 1 \<and>
                        ((x^2 / (x - 1)^2) + 
                         (y^2 / (y - 1)^2) + 
                         (z^2 / (z - 1)^2) = 1))"

(*Ovde je problem jer na znam kako da kazem ovo 
  x iz rat, y iz rat, z iz rat pa vazi resenje x y z
*)

(*Ovo sto napisah ovde verovatno nema veze sa zivotom*)
lemma deo_pod_b:
  fixes x y z :: "rat"
  shows "infinite {resenje x y z}"
  unfolding jedno_resenje_def
  sorry

text \<open>
    Drugi deo seminarskog
    
    Prvo uvodimo naredne smene
    a = x / (x - 1) => x = a / (a - 1)
    b = y / (y - 1) => x = b / (b - 1)
    c = z / (z - 1) => x = c / (c - 1)
    
    Cilj leme se transformise u
    (x^2 / (x - 1)^2) + 
    (y^2 / (y - 1)^2) +     => a^2 + b^2 + c^2 \<ge> 1
    (z^2 / (z - 1)^2) \<ge> 1

    Uslovi x \<noteq> 1 /\ y \<noteq> 1 /\ z \<noteq> 1 /\ x * y * z = 1
    se transformisu u
    a + b + c = a*b + b*c + c*a + 1
    Ovo nije tako ocigledno, pa cemo i dokazati
\<close>
(*Narednom lemom dokazujemo da vazi
  a = x / (x - 1) => x = a / (a - 1)
  b = y / (y - 1) => x = b / (b - 1)
  c = z / (z - 1) => x = c / (c - 1)
*)
lemma inverz_smene[simp]:
  fixes x :: "real"
  assumes "x \<noteq> 1"
  assumes "a = x / (x - 1)"
  shows "x = a / (a - 1)"
  using assms
proof-
  have "a * (x - 1) = x" using assms by simp
  then have "a*x - a = x" by (simp add: algebra_simps)
  then have "a*x - x = a" by (simp add: algebra_simps)
  then have "(a - 1)*x = a" by (simp add: algebra_simps)
  then show "x = a / (a - 1)"
    by (metis \<open>a * (x - 1) = x\<close> divide_divide_eq_left divide_eq_0_iff divide_eq_1_iff)
qed

(*
  Narednom lemom pokazujemo da uslov
  x*y*z = 1 nakon smene postaje
  a + b + c = a*b + b*c + c*a +1
*)
lemma transformisani_uslovi:
  fixes x y z :: "real"
  assumes "x \<noteq> 1" "y \<noteq> 1" "z \<noteq> 1"
  assumes "x * y * z = 1"
  assumes "a = x / (x - 1)"
  assumes "b = y / (y - 1)"
  assumes "c = z / (z - 1)"
  shows "a + b + c = a*b + b*c + a*c + 1"
  using assms
proof-
  have "x = a / (a - 1)"
    using assms(1) assms(5) inverz_smene by blast
  then have "y = b / (b - 1)"
    using assms(2) assms(6) inverz_smene by blast
  then have "z = c / (c - 1)"
    using assms(3) assms(7) inverz_smene by presburger
  then have "x * y * z = (a / (a - 1)) * (b / (b - 1)) * (c / (c - 1))"
    using \<open>x = a / (a - 1)\<close> \<open>y = b / (b - 1)\<close> by presburger
  then have "\<dots> = 1"
    using assms(4) by presburger
  then have "a * b * c = (a - 1) * (b - 1) * (c - 1)"
    by simp
  then have "\<dots> = (a*b - a -b + 1) * (c - 1)"
    by (metis (no_types, hide_lams) diff_add_eq diff_diff_eq2 left_diff_distrib' mult.commute mult.left_neutral)
  then have "\<dots> = a*b*c - a*b - a*c + a - b*c + b + c - 1"
    by (simp add: algebra_simps)
  then have "a*b*c = a*b*c - a*b - a*c + a - b*c + b + c - 1"
    using \<open>(a - 1) * (b - 1) * (c - 1) = (a * b - a - b + 1) * (c - 1)\<close> \<open>a * b * c = (a - 1) * (b - 1) * (c - 1)\<close> by presburger
  then have "0 = -a*b - b*c - a*c + a + b + c -1" by simp
  then show "a + b + c = a*b + b*c + a*c +1" by (simp add: algebra_simps)
qed

(*Naravno da ovoga nema, pa moram ja rucno da dokazem*)
find_theorems "(_ + _ + _)^2" 

lemma kvadrat_trinoma:
  fixes x y z :: "real"
  shows "(x + y + z)^2 = x^2 + y^2 + z^2 + 2*x*y + 2*y*z + 2*x*z"
  by (simp add: distrib_right power2_sum)

(*
  Narednom lemom se dokazuje deo po a
*)
lemma transformisana_nejednakost:
  fixes a b c :: "real"
  assumes "a + b+ c = a*b + b*c + c*a + 1"
  shows "a^2 + b^2 + c^2 \<ge> 1"
  using assms
proof-
  have "a^2 + b^2 + c^2 = (a + b + c)^2 - 2*(a*b + b*c + a*c)"
    using kvadrat_trinoma by auto
  then have "\<dots> = (a + b + c)^2 -2*(a + b + c -1)"
    by (simp add: assms)
  then have "\<dots> = (a + b + c)^2 -2*(a + b + c) + 2"
    by fastforce
  then have "\<dots> = (a + b + c - 1)^2 + 1"
    by (simp add: power2_diff)
  then have "\<dots> \<ge> 1" by simp
  then show ?thesis
    using \<open>(a + b + c)\<^sup>2 - 2 * (a * b + b * c + a * c) = (a + b + c)\<^sup>2 - 2 * (a + b + c - 1)\<close> \<open>(a + b + c)\<^sup>2 - 2 * (a + b + c - 1) = (a + b + c)\<^sup>2 - 2 * (a + b + c) + 2\<close> \<open>(a + b + c)\<^sup>2 - 2 * (a + b + c) + 2 = (a + b + c - 1)\<^sup>2 + 1\<close> \<open>a\<^sup>2 + b\<^sup>2 + c\<^sup>2 = (a + b + c)\<^sup>2 - 2 * (a * b + b * c + a * c)\<close> by presburger
qed

end