theory mr16269_Luka_HadziDjokic
  imports Main
          HOL.Rat
          "HOL-Computational_Algebra.Primes"
          "HOL-Library.Code_Target_Numeral"

begin

section "Prvi seminarski"

text "Peti zadatak sa USAMO 2019:
https://artofproblemsolving.com/wiki/index.php/2019_USAMO_Problems/Problem_5

Dva racionalna broja m/n i n/m napisana su na tabli,
gde su m i n međusobno prosti, pozitivni celi brojevi.
U svakom koraku, igrač može da izabere dva broja x i y sa table
i na nju napiše ili njihovu aritmetičku sredinu (x+y)/2 ili njihovu
harmonijsku sredinu 2xy/(x+y). Dokazati da se za sve parove (m, n)
za koje važi m + n = 2^k može napisati 1 na tabli u konačno
mnogo koraka."

text "Pored potrebnih definicija, date su i dokazane neke osnovne leme koje
malo olakšavaju rad sa njima. Prve definicije se odnose na liste. 
Te funkcije su efikasnije, pa su zato sačuvane. 
Radi pojednostavljenja iskaza glavne leme (i potencijalnog dokaza), 
definisane su ekvivalentne funkcije nad skupovima."

subsection "Definicije nad listama"

definition init_list :: "int \<Rightarrow> int \<Rightarrow> rat list" where
  "init_list m n = [Fract m n, Fract n m]"

definition a_means_list :: "rat list \<Rightarrow> rat list" where
  "a_means_list xs = map (\<lambda> (m, n). (m + n)/2) (List.product xs xs)"

definition h_means_list :: "rat list \<Rightarrow> rat list" where
  "h_means_list xs = map (\<lambda> (m, n). 2*m*n/(m+n)) (List.product xs xs)"

definition expand_list :: "rat list \<Rightarrow> rat list" where
  "expand_list xs = remdups (xs @ a_means_list xs
                           @ h_means_list xs)"

value "set ((expand_list ^^ 3) (init_list 3 5))"

subsection "Definicije nad skupovima"

definition init_set :: "int \<Rightarrow> int \<Rightarrow> rat set" where
  "init_set m n = {Fract m n, Fract n m}"

definition a_means :: "rat set \<Rightarrow> rat set" where
  "a_means S = image (\<lambda> (m, n). (m + n)/2) (S \<times> S)"

lemma a_means_lemma[simp]:
  fixes x y :: rat
  assumes "x \<noteq> y"
    and "x \<in> S"
    and "y \<in> S"
  shows "(x + y)/2 \<in> a_means S"
  using a_means_def assms(2) assms(3)
  by auto

definition h_means :: "rat set \<Rightarrow> rat set" where
  "h_means S = image (\<lambda> (m, n). 2*m*n/(m+n)) (S \<times> S)"

lemma h_means_lemma[simp]:
  fixes x y :: rat
  assumes "x \<noteq> y"
    and "x \<in> S"
    and "y \<in> S"
  shows "2*x*y/(x+y) \<in> h_means S"
  using h_means_def assms(2) assms(3)
  by auto

definition expand :: "rat set \<Rightarrow> rat set" where
  "expand S = S \<union> a_means S \<union> h_means S"

lemma preservation[simp]:
  shows "x \<in> S \<longrightarrow> x \<in> expand S"
  using expand_def
  by auto

lemma a_means_expand[simp]:
  shows "x \<in> a_means S \<longrightarrow> x \<in> expand S"
  using expand_def
  by auto

lemma h_means_expand[simp]:
  shows "x \<in> h_means S \<longrightarrow> x \<in> expand S"
  using expand_def
  by auto

lemma expand_step[simp]:
  fixes x y :: rat
  assumes "x \<noteq> y"
    and "x \<in> S"
    and "y \<in> S"
  shows "(x + y)/2 \<in> expand S \<and> 2*x*y/(x+y) \<in> expand S"
  using assms
  by simp

subsection "Glavna lema"

lemma problem_lemma:
  fixes m n :: int
  assumes "m > 0 \<and> n > 0"
    and "coprime m n"
    and "odd m \<and> odd n"
    and "\<exists> k. 2^k = m + n"
  shows "\<exists> t. 1 \<in> (expand ^^ t) (init_set m n)"
  sorry

end