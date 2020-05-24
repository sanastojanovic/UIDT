theory mi16128_Dimitrije_Antic
imports Main Complex_Main HOL.Set "HOL-Library.Infinite_Set"

begin

text\<open>
    Zadatak 2, dan 1. sa linka:
      https://imomath.com/srb/zadaci/2008_mmo.pdf

    2. (a) Dokazati da je x^2 / (x - 1)^2 + y^2 / (y - 1)^2 + z^2 / (z - 1)^2 \<ge> 1
           za sve realne brojeve x, y, z takve da nijedan od njih nije jedna 1 i za
           koje vazi xyz = 1.
       (b) Dokazati da se jednakost dostize za beskonacno mnogo trojki racionalnih
           bojeva x, y, z takvih da nijedan od njih nije jedna 1 i za koje vazi xyz = 1.

    Formulacija problema je data na 3 nacina, od kojih ce samo poslednji biti dokazan kao deo drugog seminarskog!
    \<close>

text\<open>Deo a)\<close>
lemma nejednakost_formulacija:
  assumes "(\<forall> x y z :: real. x \<noteq> 1 \<and> y \<noteq> 1 \<and> z \<noteq> 1 \<and> x * y * z = 1)"
  shows "x^2 / (x - 1)^2 
        + y^2 / (y - 1)^2 
        + z^2 / (z - 1)^2 \<ge> 1"
  (* sledgehamer resenje: using assms by blast*)
  sorry


type_synonym trojka_racionalnih = "rat \<times> rat \<times> rat"

text\<open>Samo za I seminarski, deo b): koriscenjem infinite\<close>

fun resenje :: "trojka_racionalnih \<Rightarrow> bool" where
  "resenje (x, y, z) = (x \<noteq> 1 \<and> y \<noteq> 1 \<and> z \<noteq> 1 \<and> x * y * z = 1  \<and>
                        x^2 / (x - 1)^2 
                        + y^2 / (y - 1)^2 
                        + z^2 / (z - 1)^2 = 1)"


lemma beskonacno_celih_resenja:
  "infinite {t :: trojka_racionalnih. resenje t} \<longleftrightarrow> True"
  sorry


text\<open>Samo za I seminarski, deo b): definisanjem beskonacnog skupa\<close>

inductive konacan_skup :: "'a set \<Rightarrow> bool"
  where
    "konacan_skup {}"
  | "konacan_skup A \<Longrightarrow> konacan_skup (insert a A)"
  
abbreviation beskonacan_skup :: "'a set \<Rightarrow> bool" where
  "beskonacan_skup A == \<not> konacan_skup A"

lemma beskonacno_celih_resenja':
  "beskonacan_skup {t :: trojka_racionalnih. resenje t} \<longleftrightarrow> True"
  sorry


text
\<open>
    Pocetak drugog seminarskog
\<close>

text
\<open>
    Za dokaz ce biti potrebno nekoliko pomocnih lema.
    
    Nakon uvodjenja smene a = x / (x - 1), b = y / (y - 1), c = z / (z - 1)

    Lako se vidi da nejednakost postaje a^2 + b^2 + c^2 >= 1.

    Takodje, uslov x != 1 /\ y != 1 /\ z != 1 /\ x*y*z = 1, postaje a + b + c = a*b + b*c + c*a + 1. Ta jednakost nije ocigledna,
    i bice dokazana u sledecoj lemi.
\<close>

lemma inverz_smene[simp]:
  fixes x :: real
  assumes "x \<noteq> 1"
  assumes "a = x / (x-1)"
  shows "x = a / (a-1)"
  using assms
proof-
  have "a * (x-1) = x"
    using assms
    by simp
  then have "a * x - a = x"
    by (simp add: algebra_simps)
  then have "a * x - x = a"
    by (simp add: algebra_simps)
  then have "x * (a - 1) = a"
    by (simp add: algebra_simps)
  then show "x = a / (a-1)"
    by (metis \<open>a * x - x = a\<close> add.left_neutral diff_eq_eq divide_divide_eq_left' one_eq_divide_iff)
qed


lemma uslov_nakon_smene:
  fixes x y z :: real
  assumes "x \<noteq> 1"
  assumes "y \<noteq> 1"
  assumes "z \<noteq> 1"
  assumes "x * y * z = 1"
  assumes "a = x / (x-1)"
  assumes "b = y / (y-1)"
  assumes "c = z / (z-1)"
  shows "a + b + c = a*b + b*c + a*c + 1"
  using assms
proof-
  have "x = a / (a-1)"
    using assms(1) assms(5) inverz_smene by blast
  then have "y = b / (b-1)"
    using assms(2) assms(6) inverz_smene by blast
  then have "z = c / (c-1)"
    using assms(3) assms(7) inverz_smene by blast
  then have "x * y * z = a / (a-1) * b / (b-1) * c / (c-1)"
    using `x = a / (a-1)` `y = b / (b-1)` `z = c / (c-1)`
    by fastforce
  then have "a / (a-1) * b / (b-1) * c / (c-1) = 1"
    using `x * y * z = a / (a-1) * b / (b-1) * c / (c-1)`
    using assms(4) by linarith
  then have "a * b * c = (a - 1) * (b - 1) * (c - 1)"
    by (simp add: algebra_simps)
  then have "(a - 1) * (b - 1) * (c - 1) = a*b*c - a*b - a*c + a - b*c + b + c - 1"
    by (simp add: algebra_simps)
  then have "a*b*c = a*b*c - a*b - a*c + a - b*c + b + c - 1"
    using `a * b * c = (a - 1) * (b - 1) * (c - 1)`
    by simp
  then have "0 = -a*b - b*c - a*c + a + b + c - 1"
    by simp
  then show ?thesis
    by (simp add: algebra_simps)
qed

lemma kvadrat_trinoma:
  fixes a b c :: real
  shows "(a + b + c) ^ 2 = a^2 + b^2 + c^2 + 2*a*b + 2*b*c + 2*a*c"
proof-
  have "(a+b+c)^2 = (a+b+c)*(a+b+c)"
    by (simp add: power2_eq_square)
  also have "... = a^2 + a*b + a*c + a*b + b^2 + b*c + a*c + b*c + c^2"
  proof -
    have "(a + b + c) * (a + b + c) = a * a + a * b + a * c + a * b + b * b + b * c + a * c + b * c + c * c"
      by (simp add: distrib_left mult.commute)
    then show ?thesis
      by (metis semiring_normalization_rules(29))
  qed
  finally show ?thesis
    by (simp add: algebra_simps)
qed

lemma kvadrat_binoma:
  fixes a b :: real
  shows "(a - b) ^ 2 = a^2 - 2*a*b + b^2"
proof-
  have "(a - b) ^ 2 = a^2 + b^2 - 2*a*b"
    using power2_diff by blast
  then show ?thesis
    by simp
qed

find_theorems "(_ - _)^2"

lemma pomocna_trinom:
  fixes a b c :: real
  shows "(a + b + c) ^ 2 = a^2 + b^2 + c^2 + 2*a*b + 2*b*c + 2*a*c"
proof-
  have "(a + b + c) ^ 2 = a^2 + b^2 + c^2 + 2*a*b + 2*b*c + 2*a*c"
    using kvadrat_trinoma
    by simp
  then show ?thesis
    by (simp add: algebra_simps)
qed

lemma nejednakost_nakon_smene:
  fixes a b c :: real
  assumes "a + b + c = a*b + b*c + c*a + 1"
  shows "a^2 + b^2 + c^2 \<ge> 1"
  using assms
proof-
  have "a^2 + b^2 + c^2 = (a + b + c) ^ 2 - 2*(a*b + b*c + a*c)"
    using pomocna_trinom
    by auto
  also have "... = (a + b + c) ^ 2 - 2*(a + b + c - 1)"
    using assms
    by simp
  also have "... = (a + b + c) ^ 2 - 2*(a + b + c) + 2"
    by (simp add: algebra_simps)
  also have "... = (a + b + c - 1)^2 + 1"
    using kvadrat_binoma
    by auto
  also have "... \<ge> 1"
    by simp
  finally show ?thesis
    by auto
qed

text
\<open>
  deo b): koriscenjem drugog oblika nejednakosti
  Ovde ce biti dat i dokaz kao deo drugog seminarskog!

  Kako bi dokazali da postoji beskonacno mnogo racionalnih trojki, potrebno je da pokazemo pomocnu lemu
  Kada zapravo u zadatoj nejednakosti vazi jednakost.
\<close>

lemma vazi_jednakost:
  fixes a b c :: real
  assumes "a + b + c = 1"
  assumes "a*b + b*c + a*c = 0"
  shows "a^2 + b^2 + c^2 = 1"
  using assms
proof-
  have "a^2 + b^2 + c^2 = (a+b+c)^2 - 2*(a*b + b*c + a*c)"
    using pomocna_trinom
    by auto
  also have "... = 1 - 0"
    using assms
    by simp
  finally show ?thesis
    by auto
qed

fun resenje_posle_smene :: "trojka_racionalnih \<Rightarrow> bool" where
  "resenje_posle_smene (a, b, c) = (a + b + c = 1 \<and> a*b + b*c + c*a = 0)"

value "resenje_posle_smene (2/3, 2/3, -1/3)"

text
\<open>
  Lema beskonacno_celih_resenja' je upravo zadatak pod b). Naravno, uslov moze biti jos opstiji.
  Samim tim sto za svako resenje jednakosti, nadjemo resenje koje je vece od njega, dokazali smo 
  da je skup brojeva koji zadovoljavaju gore navedene uslove beskonacan.

  Formulacija se oslanja na cinjenucu da imamo "parametrizovanu" trojku resenja preko samo jednog
  parametra t koji je racionalan broj. Odnosno, dobijamo trojku koja jeste resenje jednakosti, gde
  su sva tri clana uredjene trojke izrazena preko jednog istog racionalnog broja. A onda lemu beskonacno_celih_brojeva''
  primenjujemo na t i t1 = t+1 (kao sto je navedeno, dovoljno je da t1 > t).
  
  Zapravo je dovoljno stati kada se resenja parametrizuju jer znamo da je skup racionalnih brojeva beskonacan.


  Kako znamo da se jednakost postize za a + b + c = 1, i a*b + b*c + a*c = 0, transformisanjem te dve
  jednacine dobijamo parametrizovan oblik resenja.
  Ako c = 1 - a - b i b = t*a za neki racionalan broj t zamenimo u drugu jednacinu dobijamo:
  (t^2 + t + 1) * a^2 = (t+1) * a pa odatle imamo da su resenja oblika:
  a = (t+1) / (t^2 + t + 1), b = t * a = (t^2 + t) / (t^2 + t + 1) i c = 1 - a - b = (-t) / (t^2 + t + 1)

  Kako se radi o racionalnim brojevima, za svaka dva broja a, b postoji x tako da je a = x * b pri uslovu da je b != 0.
  Sto je u nasem slucaju ispunjeno. Iz uslova je jasno da a, b, c u isto vreme ne mogu biti 0 zbog a*b + b*c + a*c = 0,
  tako da opisanu transformaciju uvek mozemo uraditi. U dokazu su izabrani a i b bez guljenja na opstosti.

  Objasnjeni postupak dokazuje lema beskonacno_resenja, uz koriscenje i pomocna_1 i pomocna_2.
\<close>

lemma beskonacno_celih_resenja'':
  fixes t :: rat
  assumes "resenje_posle_smene ( (t+1)/(t^2 + t + 1), (t^2 + t)/(t^2 + t + 1), (-t)/(t^2 + t + 1) )"
  shows "\<exists> t1 :: rat. t1 = t + 1 \<and> resenje_posle_smene ( (t1+1)/(t1^2 + t1 + 1), (t1^2 + t1)/(t1^2 + t1 + 1), (-t1)/(t1^2 + t1 + 1) ) "
  using assms
  sorry

lemma pomocna_1:
  fixes t :: rat
  shows "t^2 + t + 1 \<noteq> 0"
  by (smt add_diff_cancel_left' dbl_def dbl_simps(2) is_num_normalize(1) le_add_same_cancel1 mult.right_neutral mult_2 one_power2 power2_sum semiring_normalization_rules(23) sum_power2_ge_zero sum_power2_le_zero_iff uminus_add_conv_diff zero_neq_one)


lemma pomocna_2:
  fixes a b c d :: rat
  assumes "a + b + c = 1"
  assumes "a*b + b*c + a*c = 0"
  shows "a \<noteq> 0 \<or> b \<noteq> 0 \<or> c \<noteq> 0"
  using assms
  by linarith

lemma beskonacno_resenja:
  fixes a b c t :: rat
  assumes "a + b + c = 1"
  assumes "a*b + b*c + a*c = 0"
  assumes "b = t*a"
  assumes "a \<noteq> 0" (* Pretpostavka sledi iz leme pomocna_2, bez gubljenja na opstosti *)
  shows "(t+1)/(t^2 + t + 1) + (t^2 + t)/(t^2 + t + 1) + (-t)/(t^2 + t + 1) = 1 
          \<and>
          (t+1)/(t^2 + t + 1) * (t^2 + t)/(t^2 + t + 1) + (t^2 + t)/(t^2 + t + 1) * (-t)/(t^2 + t + 1) + (t+1)/(t^2 + t + 1) * (-t)/(t^2 + t + 1)=0"
  using assms
proof-
  have "c = 1 - b - a"
    using assms(1)
    by simp
  then have "a * t * a + t * a * (1 - b - a) + a * (1 - b - a) = 0"
    using `c = 1 - b - a` assms(3) assms(2)
    by simp
  then have "a^2 * t + t * a - t * a * t * a - t * a^2 + a - a * t * a - a^2 = 0"
    using assms(3)
    by (smt add_diff_eq mult.commute mult.right_neutral right_diff_distrib' semiring_normalization_rules(18) semiring_normalization_rules(29))
  then have "a^2 * t^2 + a^2 * t + a^2 - a * t - a = 0"
    by (smt diff_add_eq_diff_diff_swap diff_right_commute eq_iff_diff_eq_0 mult.commute semiring_normalization_rules(18) semiring_normalization_rules(29))
  then have "a^2 * (t^2 + t + 1) - a * (t + 1) = 0"
    by (simp add: algebra_simps)
  then have "a * (t^2 + t + 1) = t + 1"
    using assms(4)
    by (metis (no_types, lifting) eq_iff_diff_eq_0 mult_cancel_left numeral_One power_add_numeral2 power_one_right semiring_norm(2))
  then have "a = (t + 1) / (t^2 + t + 1)"
    using pomocna_1[of t]
    by (simp add: eq_divide_eq)
  then have "b = (t^2 + t) / (t^2 + t + 1)"
    using assms (3)
    by (simp add: distrib_left semiring_normalization_rules(29))
  then have "c = (-t) / (t^2 + t + 1)"
    using `c = 1 - b - a` `b = (t^2 + t) / (t^2 + t + 1)` `a = (t + 1) / (t^2 + t + 1)`
    by (metis add.commute add_diff_cancel_right' diff_divide_distrib diff_rat_def pomocna_1 right_inverse_eq)
  then show ?thesis
    using `b = (t^2 + t) / (t^2 + t + 1)` `a = (t + 1) / (t^2 + t + 1)` `c = (-t) / (t^2 + t + 1)` assms
    by simp    
qed

end

