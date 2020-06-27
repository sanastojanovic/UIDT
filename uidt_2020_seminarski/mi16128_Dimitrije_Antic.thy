text\<open>
    Zadatak 2, dan 1. sa linka:
      https://imomath.com/srb/zadaci/2008_mmo.pdf

    2. (a) Dokazati da je x^2 / (x - 1)^2 + y^2 / (y - 1)^2 + z^2 / (z - 1)^2 \<ge> 1
           za sve realne brojeve x, y, z takve da nijedan od njih nije jedna 1 i za
           koje vazi xyz = 1.
       (b) Dokazati da se jednakost dostize za beskonacno mnogo trojki racionalnih
           bojeva x, y, z takvih da nijedan od njih nije jednak 1 i za koje vazi xyz = 1.
    \<close>

theory mi16128_Dimitrije_Antic
imports Main Complex_Main HOL.Set "HOL-Library.Infinite_Set"

begin

text\<open>Prvi seminarski: formulisanje problema\<close>
lemma nejednakost_formulacija:
  fixes x y z :: real
  assumes "x \<noteq> 1" "x \<noteq> 1" "x \<noteq> 1" "x * y * z = 1"
  shows "x^2 / (x - 1)^2 
        + y^2 / (y - 1)^2 
        + z^2 / (z - 1)^2 \<ge> 1"
  using assms
  sorry


type_synonym rat3 = "rat \<times> rat \<times> rat"
fun resenje :: "rat3 \<Rightarrow> bool" where
  "resenje (x, y, z) = (x \<noteq> 1 \<and> y \<noteq> 1 \<and> z \<noteq> 1 \<and> x * y * z = 1  \<and>
                        x^2 / (x - 1)^2 
                        + y^2 / (y - 1)^2 
                        + z^2 / (z - 1)^2 = 1)"

lemma beskonacno_celih_resenja:
  "infinite {t \<in> (\<rat> \<times> \<rat> \<times> \<rat>). resenje t}"
  sorry


text
\<open>
    U nastavku je drugi seminarski.
\<close>

text
\<open>
    Za dokaz ce biti potrebno nekoliko pomocnih lema.
    
    Nakon uvodjenja smene a = x / (x - 1), b = y / (y - 1), c = z / (z - 1)

    Lako se vidi da nejednakost postaje a^2 + b^2 + c^2 >= 1.

    Takodje, uslov x != 1 /\ y != 1 /\ z != 1 /\ x*y*z = 1, postaje a + b + c = a*b + b*c + c*a + 1. Ta jednakost nije ocigledna,
    i bice dokazana u lemi uslov_nakon_smene.
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
  assumes "x \<noteq> 1" "y \<noteq> 1" "z \<noteq> 1" "x * y * z = 1" "a = x / (x-1)" "b = y / (y-1)" "c = z / (z-1)"
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
  by (simp add: field_simps power2_eq_square)

find_theorems "(_ - _)^2"

find_theorems "(_ + _ + _)^2"

text
\<open>Sledeca lema dokazuje nejednakost, odnosno deo pod a).\<close>
lemma nejednakost_nakon_smene:
  fixes a b c :: real
  assumes "a + b + c = a*b + b*c + c*a + 1"
  shows "a^2 + b^2 + c^2 \<ge> 1"
  using assms
proof-
  have "a^2 + b^2 + c^2 = (a + b + c) ^ 2 - 2*(a*b + b*c + a*c)"
    using kvadrat_trinoma
    by auto
  also have "... = (a + b + c) ^ 2 - 2*(a + b + c - 1)"
    using assms
    by simp
  also have "... = (a + b + c) ^ 2 - 2*(a + b + c) + 2"
    by (simp add: algebra_simps)
  also have "... = (a + b + c - 1)^2 + 1"
    by (simp add: power2_diff)
  also have "... \<ge> 1"
    by simp
  finally show ?thesis
    by auto
qed

text
\<open>
  deo b): koriscenjem drugog oblika nejednakosti

  Za pocetak potrebno je da pokazemo pomocnu lemu koja pokazuje
  kada zapravo u zadatoj nejednakosti vazi jednakost.
\<close>

lemma vazi_jednakost:
  fixes a b c :: real
  assumes "a + b + c = 1" "a*b + b*c + a*c = 0"
  shows "a^2 + b^2 + c^2 = 1"
  using assms
proof-
  have "a^2 + b^2 + c^2 = (a+b+c)^2 - 2*(a*b + b*c + a*c)"
    using kvadrat_trinoma
    by auto
  also have "... = 1 - 0"
    using assms
    by simp
  finally show ?thesis
    by auto
qed

text
\<open>Pomocna funkcija radi provere \<close>
fun resenje_posle_smene :: "rat3 \<Rightarrow> bool" where
  "resenje_posle_smene (a, b, c) = (a + b + c = 1 \<and> a*b + b*c + c*a = 0)"
value "resenje_posle_smene (2/3, 2/3, -1/3)"

lemma pomocna_1:
  fixes t :: rat
  shows "t^2 + t + 1 \<noteq> 0"
  by (smt add_diff_cancel_left' dbl_def dbl_simps(2) is_num_normalize(1) le_add_same_cancel1 mult.right_neutral mult_2 one_power2 power2_sum semiring_normalization_rules(23) sum_power2_ge_zero sum_power2_le_zero_iff uminus_add_conv_diff zero_neq_one)

text
\<open>
  Kako se radi o racionalnim brojevima, za svaka dva broja a, b postoji x tako da je a = x * b pri uslovu da je b != 0.
  Cinjenicu da je bar jedan od brojeva a, b, c ~= 0 dokazuje lema pomocna_2.
  Cinjenicu postojanja broja x dokazuje lema pomocna_3.
\<close>
lemma pomocna_2:
  fixes a b c d :: rat
  assumes "a + b + c = 1" "a*b + b*c + a*c = 0"
  shows "a \<noteq> 0 \<or> b \<noteq> 0 \<or> c \<noteq> 0"
  using assms
  by linarith

lemma pomocna_3:
  fixes a b :: rat
  assumes "b \<noteq> 0"
  shows "\<exists> t :: rat. a = t * b"
  using assms
  by (metis dvdE dvd_field_iff linordered_field_class.sign_simps(24))

text
\<open>
  Sledeca lema opisuje postupak parametrizacije trojke a, b, c preko jednog racionalnog broja t.
  Cilj je svesti trazenje trojke a, b, c na trazenje jednog racionalnog broja. 


  Na osnovu prethodne dve leme, parametrizacija je uvek moguca kako je makar jedan od brojeva
  a, b, c ~= 0. U dokazu ce biti koriscena cinjenica da je a ~= 0, bez gubljenja na opstosti.

  Kako iz leme vazi_jednakost znamo da se jednakost postize za a + b + c = 1, i a*b + b*c + a*c = 0, transformisanjem te dve
  jednacine dobijamo parametrizovan oblik resenja.
  Ako c = 1 - a - b i b = t*a za neki racionalan broj t zamenimo u drugu jednacinu dobijamo:
  (t^2 + t + 1) * a^2 = (t+1) * a pa odatle imamo da su resenja oblika:
  a = (t+1) / (t^2 + t + 1), b = t * a = (t^2 + t) / (t^2 + t + 1) i c = 1 - a - b = (-t) / (t^2 + t + 1)
\<close>

lemma parametrizacija_jednakosti:
  fixes a b c :: rat
  assumes "a + b + c = 1" "a*b + b*c + a*c = 0" "a \<noteq> 0"
  shows "(\<exists>t :: rat. b = t * a \<and> (t+1)/(t^2 + t + 1) + (t^2 + t)/(t^2 + t + 1) + (-t)/(t^2 + t + 1) = 1 
          \<and>
          (t+1)/(t^2 + t + 1) * (t^2 + t)/(t^2 + t + 1) + (t^2 + t)/(t^2 + t + 1) * (-t)/(t^2 + t + 1) + (t+1)/(t^2 + t + 1) * (-t)/(t^2 + t + 1)=0)"
  using assms
proof-
  have "c = 1 - b - a"
    using assms(1) by auto
  then obtain "t" where "b = t * a"
    using assms(3) pomocna_3 by blast
  then have "a * t * a + t * a * (1 - b - a) + a * (1 - b - a) = 0"
    using \<open>c = 1 - b - a\<close> assms(2) by auto
  then have "a^2 * t + t * a - t * a * t * a - t * a^2 + a - a * t * a - a^2 = 0"
    by (smt \<open>b = t * a\<close> add_diff_eq mult.commute mult.right_neutral right_diff_distrib' semiring_normalization_rules(18) semiring_normalization_rules(29))
  then have "a^2 * t^2 + a^2 * t + a^2 - a * t - a = 0"
    by (smt diff_add_eq_diff_diff_swap diff_right_commute eq_iff_diff_eq_0 mult.commute semiring_normalization_rules(18) semiring_normalization_rules(29))
  then have "a^2 * (t^2 + t + 1) - a * (t + 1) = 0"
    by (simp add: algebra_simps)
  then have "a * (t^2 + t + 1) = t + 1"
    by (metis (no_types, lifting) assms(3) eq_iff_diff_eq_0 mult_cancel_left numeral_One power_add_numeral2 power_one_right semiring_norm(2))
  then have "a = (t + 1) / (t^2 + t + 1)"
    by (simp add: eq_divide_eq pomocna_1)
  then have "b = (t^2 + t) / (t^2 + t + 1)"
    by (simp add: \<open>b = t * a\<close> distrib_left power2_eq_square)
  then have "c = (-t) / (t^2 + t + 1)"
    by (simp add: \<open>a = (t + 1) / (t\<^sup>2 + t + 1)\<close> \<open>c = 1 - b - a\<close> add_divide_eq_if_simps(4) pomocna_1)
  then show ?thesis
    using \<open>a = (t + 1) / (t\<^sup>2 + t + 1)\<close> \<open>b = (t\<^sup>2 + t) / (t\<^sup>2 + t + 1)\<close> \<open>b = t * a\<close> assms(1) assms(2) by auto
qed


text
\<open>
  Lema proizvoljno_t dokazuje da su, prethodno izvedeni, uslovi jednakosti zadovoljeni za bilo koji racionalni broj t,
  koji je dobijen prethodno opisanim/dokazanim postupkom parametrizacije.
\<close>

definition resenje_po_t :: "rat \<Rightarrow> bool" where
"resenje_po_t t = (
  (t+1)/(t^2 + t + 1) + (t^2 + t)/(t^2 + t + 1) + (-t)/(t^2 + t + 1) = 1 
  \<and>
  (t+1)/(t^2 + t + 1) * (t^2 + t)/(t^2 + t + 1) + 
  (t^2 + t)/(t^2 + t + 1) * (-t)/(t^2 + t + 1) + 
  (t+1)/(t^2 + t + 1) * (-t)/(t^2 + t + 1) = 0
)"

lemma proizvoljno_t:
  fixes t :: rat
  shows "resenje_po_t t"
  unfolding resenje_po_t_def
proof
  show "(t+1)/(t^2 + t + 1) + (t^2 + t)/(t^2 + t + 1) + (-t)/(t^2 + t + 1) = 1"
    by (smt add_diff_cancel_left' add_divide_eq_if_simps(1) diff_rat_def eq_divide_eq pomocna_1 right_inverse_eq semiring_normalization_rules(23))
next
  show "(t+1)/(t^2 + t + 1) * (t^2 + t)/(t^2 + t + 1) + (t^2 + t)/(t^2 + t + 1) * (-t)/(t^2 + t + 1) + (t+1)/(t^2 + t + 1) * (-t)/(t^2 + t + 1)=0"
    by (smt add.inverse_inverse add_diff_cancel_left' diff_minus_eq_add distrib_left eq_iff_diff_eq_0 mult.left_commute mult_minus1_right mult_minus_right power2_eq_square times_divide_eq_left)
qed

find_theorems "infinite _"

text
\<open>
  Konacan dokaz je dat u teoremi beskonacno_mnogo_resenja. 
  Ona pokazuje da je skup racionalnih brojeva koji zadovoljavaju uslove resenja beskonacan.
\<close>

theorem beskonacno_mnogo_resenja:
  shows "infinite {x \<in> \<rat>. resenje_po_t x}"
  by (simp add: Rats_infinite proizvoljno_t)


theorem beskonacno_mnogo_resenja':
  shows "infinite {x :: rat. resenje_po_t x}"
  by (simp add: infinite_UNIV_char_0 proizvoljno_t)

end

