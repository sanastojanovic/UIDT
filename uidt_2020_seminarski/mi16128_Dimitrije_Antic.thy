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
  Sledeca lema je upravo zadatak pod b). Naravno, uslov moze biti jos opstiji.
  Samim tim sto za svako resenje jednakosti, nadjemo resenje koje je vece od njega, dokazali smo 
  da je skup brojeva koji zadovoljavaju gore navedene uslove beskonacan.

  U dokazu se koristi pomocna lema koja "parametrizuje" trojku resenja u odnosu na samo jedan
  parametar t koji je racionalan broj. Odnosno, dobijamo trojku koja jeste resenje jednakosti, gde
  su sva tri clana uredjene trojke izrazena preko jednog istog racionalnog broja. A onda gore objasnjenu
  ideju primenjujemo na t i t1 = t+1 (kao sto je navedeno, dovoljno je da t1 > t).
  
  Zapravo je dovoljno stati kada se resenja parametrizuju jer znamo da je skup racionalnih brojeva beskonacan.


  Kako znamo da se jednakost postize za a + b + c = 1, i a*b + b*c + a*c = 0, transformisanjem te dve
  jednacine dobijamo parametrizovan oblik resenja.
  Ako c = 1 - a - b i b = t*a za neki racionalan broj t zamenimo u drugu jednacinu dobijamo:
  (t^2 + t + 1) * a^2 = (t+1) * a pa odatle imamo da su resenja oblika:
  a = (t+1) / (t^2 + t + 1), b = t * a = (t^2 + t) / (t^2 + t + 1) i c = 1 - a - b = (-t) / (t^2 + t + 1)

  Time dobijamo da za svaku racionalnu trojku resenja jednakosti, 
  mozemo da nadjemo t iz Q tako da su a b i c izrazeni preko t.
\<close>


lemma beskonacno_celih_resenja'':
  fixes t :: rat
  assumes "resenje_posle_smene ( (t+1)/(t^2 + t + 1), (t^2 + t)/(t^2 + t + 1), (-t)/(t^2 + t + 1) )"
  shows "\<exists> t1 :: rat. t1 = t + 1 \<and> resenje_posle_smene ( (t1+1)/(t1^2 + t1 + 1), (t1^2 + t1)/(t1^2 + t1 + 1), (-t1)/(t1^2 + t1 + 1) ) "
  using assms
  sorry

end

