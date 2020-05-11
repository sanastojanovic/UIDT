theory mr16269_Luka_HadziDjokic
  imports Main
          HOL.Rat
          "HOL-Computational_Algebra.Primes"
          "HOL-Library.Code_Target_Numeral"

begin

text "Peti zadatak sa USAMO 2019:
https://artofproblemsolving.com/wiki/index.php/2019_USAMO_Problems/Problem_5

Dva racionalna broja m/n i n/m napisana su na tabli,
gde su m i n međusobno prosti, pozitivni celi brojevi.
U svakom koraku, igrač može da izabere dva broja x i y sa table
i na nju napiše ili njihovu aritmetičku sredinu (x+y)/2 ili njihovu
harmonijsku sredinu 2xy/(x+y). Dokazati da se za sve parove (m, n)
za koje važi m + n = 2^k može napisati 1 na tabli u konačno
mnogo koraka."

(*
  Pored potrebnih definicija, date su 
  i dokazane neke osnovne leme koje
  malo olakšavaju rad sa njima. 
*)

(*
  TODO: zameniti liste skupovima u svim definicijama,
  kako bi se izbeglo `remdups` u `expand` funkciji i
  `set (...)` u svakoj lemi.
*)

definition init_list :: "int \<Rightarrow> int \<Rightarrow> rat list" where
  "init_list m n = [Fract m n, Fract n m]"

definition a_means :: "rat list \<Rightarrow> rat list" where
  "a_means xs = map (\<lambda> (m, n). (m + n)/2) (List.product xs xs)"

lemma a_means_lemma[simp]:
  fixes x y :: rat
  assumes "x \<noteq> y"
    and "x \<in> set l"
    and "y \<in> set l"
  shows "(x + y)/2 \<in> set (a_means l)"
  using a_means_def assms(2) assms(3)
  by auto

definition h_means :: "rat list \<Rightarrow> rat list" where
  "h_means xs = map (\<lambda> (m, n). 2*m*n/(m+n)) (List.product xs xs)"

lemma h_means_lemma[simp]:
  fixes x y :: rat
  assumes "x \<noteq> y"
    and "x \<in> set l"
    and "y \<in> set l"
  shows "2*x*y/(x+y) \<in> set (h_means l)"
  using h_means_def assms(2) assms(3)
  by auto

definition expand :: "rat list \<Rightarrow> rat list" where
  "expand xs = remdups (xs @ a_means xs
                           @ h_means xs)"
lemma preservation[simp]:
  shows "x \<in> (set l) \<longrightarrow> x \<in> set (expand l)"
  using expand_def
  by auto

lemma a_means_expand[simp]:
  shows "x \<in> set (a_means l) \<longrightarrow> x \<in> set (expand l)"
  using expand_def
  by auto

lemma h_means_expand[simp]:
  shows "x \<in> set (h_means l) \<longrightarrow> x \<in> set (expand l)"
  using expand_def
  by auto

lemma expand_step[simp]:
  fixes x y :: rat
  assumes "x \<noteq> y"
    and "x \<in> set l"
    and "y \<in> set l"
  shows "(x + y)/2 \<in> set (expand l) \<and> 2*x*y/(x+y) \<in> set (expand l)"
  using assms
  by simp

(* 
  Iteracija funkcije expand je neefikasna jer 
  broj elemenata raste (eksponencijalno?),
  ali to ne utiče preterano na dokaz.
*)

value "set ((expand ^^ 3) (init_list 3 5))"

lemma problem_lemma:
  fixes m n :: int
  assumes "m > 0 \<and> n > 0"
    and "coprime m n"
    and "odd m \<and> odd n"
    and "\<exists> k. 2^k = m + n"
  shows "\<exists> t. 1 \<in> set ((expand ^^ t) (init_list m n))"
  sorry