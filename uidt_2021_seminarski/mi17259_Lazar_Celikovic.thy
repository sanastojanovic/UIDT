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

(*Drugi deo seminarskog podrazumeva da se dokaze
  da postoji beskonacno mnogo trojki racionalnih 
  brojeva koje zadovoljavaju sledecu definiciju.

  Iz tog razloga definisemo tip koji predstavlja
  trojku racionalnih brojeva*)

type_synonym rat3 = "rat \<times> rat \<times> rat"
fun jedno_resenje :: "rat3 \<Rightarrow> bool" where
"jedno_resenje (x, y, z) = (x \<noteq> 1 \<and> 
                        y \<noteq> 1 \<and> 
                        z \<noteq> 1 \<and> 
                        x * y * z = 1 \<and>
                        ((x^2 / (x - 1)^2) + 
                         (y^2 / (y - 1)^2) + 
                         (z^2 / (z - 1)^2) = 1))"

(*
  Narednom lemom tvrdimo da postoji beskonacan skup
  trojki racionalnih brojeva takvih da zadovoljavaju
  funkciju jedno_resenje
*)
lemma deo_pod_b:
  "infinite {t \<in> rat3. jedno_resenje t}"
  sorry

(*-----------------------------------------------------------------------*)

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
  assumes "a + b + c = a*b + b*c + c*a + 1"
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

(* Sada je potrebno dokazati deo pod b, odnosno da postoji
   beskonacno trojki racionalnih brojeva koji zadovoljavaju
   funkciju jedno_resenje

   Iz jednacine a^2 + b^2 + c^2 -1 = (a + b + c - 1)^2
   vidimo da nejednakost a^2 + b^2 + c^2 \<ge> 1 postaje
   jednakost ako i samo ako su a^2 + b^2 + c^2 = 1
   i a + b + c = 1
*)

lemma jednakost:
  fixes a b c :: "real"
  assumes "a + b + c = 1" "a*b + b*c + c*a = 0"
  shows "a^2 + b^2 + c^2 = 1"
  using assms
proof-
  have "a^2 + b^2 + c^2 = (a + b + c)^2 - 2*(a*b + b*c + c*a)"
    by (simp add: distrib_right power2_sum)
  then have "\<dots> = 1 - 0"
    by (simp add: assms(1) assms(2))
  then show ?thesis
    by (simp add: \<open>a\<^sup>2 + b\<^sup>2 + c\<^sup>2 = (a + b + c)\<^sup>2 - 2 * (a * b + b * c + c * a)\<close>)
qed

(*  
    Sada ce nam biti potrebno nekoliko pomocnih lema
    Prvom cemo pokazati da je bar jedan od brojeva
    a, b, c razlicit od nula
*)

lemma ne_nula:
  fixes a b c :: "rat"
  assumes "a + b + c = 1" "a*b + b*c + c*a = 0"
  shows "a \<noteq> 0 \<or> b \<noteq> 0 \<or> c \<noteq> 0"
  using assms(1) by fastforce

(*  
    Sada kada znamo da je bar jedan od brojeva a, b, c
    razlicit od nule imamo sve sto je potrebno da pokazemo
    da za svaka dva racionalna broja a i b postoji broj x
    takav da vazi a = b * x
*)

lemma postojanje_x:
  fixes a b :: "rat"
  assumes "b \<noteq> 0"
  shows "\<exists> x :: rat. a = x * b"
  by (metis assms nonzero_eq_divide_eq)

(*
    Da bi mogli da pristupimo parametrizaciji resenja
    potrebno je pokazati da vazi x^2 + x + 1 \<noteq> 0 uvek
*)

lemma razlicito_od_nula:
  fixes x :: "rat"
  shows "x^2 + x + 1 \<noteq> 0"
  by (smt (verit) add.commute add_cancel_left_left add_mono_thms_linordered_semiring(3) is_num_normalize(1) mult_2 mult_cancel_left1 not_one_le_zero one_power2 power2_sum sum_power2_ge_zero)

end