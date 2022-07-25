theory mi18030_Isidora_Slavkovic_mi18006_Slobodan_Jenko
  imports Main HOL.Rat HOL.Orderings HOL.Real
begin

text\<open>https://web.math.ucsb.edu/~agboola/teaching/2021/winter/122A/rudin.pdf\<close>

definition tacno_jedan :: "bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool"  where
  "tacno_jedan a b c \<longleftrightarrow> (a \<or> b \<or> c) \<and> (\<not>a \<or> \<not>b) \<and> (\<not>a \<or> \<not>c) \<and> (\<not>b \<or> \<not>c)"

section\<open>Uredjeni Skupovi\<close>

text\<open>1.6 Definicija\<close>
locale uredjen_skup =
  fixes manje :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infixl "\<prec>" 100)
  fixes S :: "'a set"
  assumes potpunost: "\<And>x y. \<lbrakk>x \<in> S; y \<in> S\<rbrakk> \<Longrightarrow>
                        tacno_jedan (x \<prec> y) (x = y) (y \<prec> x)"
  assumes tranzitivnost: "\<And>x y z. \<lbrakk>x \<in> S; y \<in> S; z \<in> S; x \<prec> y; y \<prec> z\<rbrakk> \<Longrightarrow> x \<prec> z"
begin

definition manje_jednako :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infixl "\<preceq>" 100) where
  "x \<preceq> y \<longleftrightarrow> x \<prec> y \<or> x = y"

definition vece :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infixl "\<succ>" 100) where
  "x \<succ> y \<longleftrightarrow> \<not> (x \<preceq> y)"

definition vece_jednako :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infixl "\<succeq>" 100) where
  "x \<succeq> y \<longleftrightarrow> x \<succ> y \<or> x = y"

text\<open>1.7 Definicija\<close>
definition ogranicen_odozgo where
  "ogranicen_odozgo E \<longleftrightarrow> (E \<subseteq> S) \<and> (\<exists> \<beta> \<in> S. (\<forall> x \<in> E. x \<preceq> \<beta>))"

definition gornja_granica where
  "gornja_granica \<beta> E \<longleftrightarrow> (E \<subseteq> S) \<and> (\<beta> \<in> S \<and> (\<forall> x \<in> E. x \<preceq> \<beta>))"

definition ogranicen_odozdo where
  "ogranicen_odozdo E \<longleftrightarrow> (E \<subseteq> S) \<and> (\<exists> \<beta> \<in> S. (\<forall> x \<in> E. x \<succeq> \<beta>))"

definition donja_granica where
  "donja_granica \<beta> E \<longleftrightarrow> (E \<subseteq> S) \<and> (\<beta> \<in> S \<and> (\<forall> x \<in> E. x \<succeq> \<beta>))"

text\<open>1.8 Definicija\<close>
definition supremum where 
  "supremum \<alpha> E \<longleftrightarrow> (E \<subseteq> S) \<and> (ogranicen_odozgo E) \<and> (\<alpha> \<in> S) \<and> 
                       (gornja_granica \<alpha> E) \<and> 
                      (\<forall> \<gamma> \<in> E. \<gamma> \<prec> \<alpha> \<longrightarrow> \<not> (gornja_granica \<gamma> E))"

definition infimum where
  "infimum \<alpha> E \<longleftrightarrow> (E \<subseteq> S) \<and> (ogranicen_odozdo E) \<and> (\<alpha> \<in> S) \<and> 
                       (donja_granica \<alpha> E) \<and> 
                      (\<forall> \<gamma> \<in> E. \<gamma> \<succ> \<alpha> \<longrightarrow> \<not> (donja_granica \<gamma> E))"

notation Set.empty ("\<emptyset> ")

text\<open>1.10 Definicija\<close>
definition ima_najmanju_gornju_granicu where 
  "ima_najmanju_gornju_granicu  \<longleftrightarrow> 
    (\<forall> E \<subseteq> S. (E \<noteq> \<emptyset>) \<and> (ogranicen_odozgo E) \<longrightarrow> (\<exists> \<alpha> \<in> S. supremum \<alpha> E))"

text\<open>1.11 Teorema\<close>
theorem T1_11: 
  assumes "ima_najmanju_gornju_granicu" and "B \<subseteq> S" and "B \<noteq> \<emptyset>" and "ogranicen_odozdo B" and
          "L = {x. x \<in> S \<and>  donja_granica x B}"
  shows "(\<exists> \<alpha> \<in> S. (supremum \<alpha> L) \<and> (infimum \<alpha> B))"
proof -
  from assms(4) assms(5) have "L \<noteq> \<emptyset>"
    using donja_granica_def ogranicen_odozdo_def by auto 
  from assms(5) have "L \<subseteq> S" by auto
  from this have \<open>\<forall> y \<in> L. \<forall> x \<in> B. y \<preceq> x\<close> 
    by (smt (verit, best) assms(5) donja_granica_def in_mono manje_jednako_def mem_Collect_eq potpunost tacno_jedan_def vece_def vece_jednako_def)
  from this \<open>L \<noteq> \<emptyset>\<close> \<open>L \<subseteq> S\<close>  have "\<forall> x \<in> B. gornja_granica x L"
    using gornja_granica_def assms(3)
    apply auto 
    using assms(2) by blast
  from this have "ogranicen_odozgo L" 
    using assms(3) gornja_granica_def ogranicen_odozgo_def by fastforce
  from this assms(1) have "\<exists> \<alpha>. supremum \<alpha> L"
    using \<open>L \<noteq> \<emptyset>\<close> \<open>L \<subseteq> S\<close> ima_najmanju_gornju_granicu_def by blast
  from this obtain \<alpha> where "supremum \<alpha> L" by auto

  from this have "\<And> \<gamma>. (\<gamma> \<in> S \<and> \<gamma> \<prec> \<alpha>) \<longrightarrow> \<not> (gornja_granica \<gamma> L)" 
    unfolding supremum_def ogranicen_odozgo_def gornja_granica_def donja_granica_def 
    using \<open>L \<noteq> \<emptyset>\<close> \<open>L \<subseteq> S\<close> \<open>ogranicen_odozgo L\<close> 
    apply auto
    sorry

  from this have "\<gamma> \<notin> B"
    sorry

  from this \<open>supremum \<alpha> L\<close> have "\<And> \<beta>. \<alpha> \<prec> \<beta> \<longrightarrow> \<beta> \<notin> L" 
    by (metis gornja_granica_def manje_jednako_def potpunost subset_iff supremum_def tacno_jedan_def)

  from this \<open>\<And>\<gamma>. \<gamma> \<in> S \<and> \<gamma> \<prec> \<alpha> \<longrightarrow> \<not> gornja_granica \<gamma> L\<close> \<open>\<forall>x\<in>B. gornja_granica x L\<close>  \<open>supremum \<alpha> L\<close>
    have "donja_granica \<alpha> B" 
    by (metis assms(2) donja_granica_def subset_iff supremum_def uredjen_skup.manje_jednako_def uredjen_skup_axioms vece_def vece_jednako_def)

  from \<open>\<And> \<beta>. \<alpha> \<prec> \<beta> \<longrightarrow> \<beta> \<notin> L\<close> have "\<And> \<beta>. \<alpha> \<prec> \<beta> \<longrightarrow> \<not> (donja_granica \<beta> B)" 
    by (simp add: assms(5) donja_granica_def)

  from this \<open>donja_granica \<alpha> B\<close> have "infimum \<alpha> B" 
    by (metis assms(4) donja_granica_def infimum_def potpunost tacno_jedan_def uredjen_skup.manje_jednako_def uredjen_skup_axioms vece_def)

  from this \<open>supremum \<alpha> L\<close> show "(\<exists> \<alpha> \<in> S. (supremum \<alpha> L) \<and> (infimum \<alpha> B))" 
    using supremum_def by blast
qed
end

definition nat_less where
  "nat_less = (less::(nat \<Rightarrow> nat \<Rightarrow> bool))"
definition nat_S where
  "nat_S = {1,2,3,4,5::nat}"

term "uredjen_skup.manje_jednako"

global_interpretation test_uredjen_skup: uredjen_skup where
  manje = nat_less and
  S = nat_S
defines uredjen_skup_supremum = 
  "uredjen_skup.supremum nat_less nat_S" and
  uredjen_skup_ogranicen_odozgo = 
  "uredjen_skup.ogranicen_odozgo nat_less nat_S" and
  uredjen_skup_gornja_granica = 
  "uredjen_skup.gornja_granica nat_less nat_S" and
  uredjen_skup_manje_jednako = 
  "uredjen_skup.manje_jednako nat_less"
unfolding tacno_jedan_def uredjen_skup_def nat_less_def nat_S_def
  by auto

value "uredjen_skup_supremum 4 {1,2,3::nat}"

value "infimum 1 {1,2,3} {0,1,2,3,4::nat}"

section \<open>Polje\<close>

text\<open>1.12 Definicija\<close>
locale Polje =
  fixes F :: "'a set"
  fixes plus :: "'a \<Rightarrow> 'a  \<Rightarrow> 'a" (infixl "\<oplus>" 200)
  fixes puta :: "'a \<Rightarrow> 'a  \<Rightarrow> 'a" (infixl "\<otimes>" 201)
  fixes nula :: "'a" ("\<zero>")
  fixes jedan :: "'a" ("\<one>")
  fixes inverz_plus :: "'a \<Rightarrow> 'a" ("\<ominus>_" 202)
  fixes inverz_puta :: "'a \<Rightarrow> 'a" ("_\<dieresis>" 203)

  assumes A1: "\<And> x y. \<lbrakk>x \<in> F; y \<in> F\<rbrakk> \<Longrightarrow> x \<oplus> y \<in> F"
  assumes A2: "\<And> x y. \<lbrakk>x \<in> F; y \<in> F\<rbrakk> \<Longrightarrow> x \<oplus> y = y \<oplus> x"
  assumes A3: "\<And> x y. \<lbrakk>x \<in> F; y \<in> F\<rbrakk> \<Longrightarrow> (x \<oplus> y) \<oplus> z = x \<oplus> (y \<oplus> z)"
  assumes A4: "\<zero> \<in> F \<and> (\<forall> x \<in> F. \<zero> \<oplus> x = x)"
  assumes A5: "\<And> x. \<lbrakk>x \<in> F\<rbrakk> \<Longrightarrow> (\<ominus>x) \<in> F \<and> x \<oplus> (\<ominus>x) = \<zero>"

  assumes M1: "\<And> x y. \<lbrakk>x \<in> F; y \<in> F\<rbrakk> \<Longrightarrow> x \<otimes> y \<in> F"
  assumes M2: "\<And> x y. \<lbrakk>x \<in> F; y \<in> F\<rbrakk> \<Longrightarrow> x \<otimes> y = y \<otimes> x"
  assumes M3: "\<And> x y. \<lbrakk>x \<in> F; y \<in> F\<rbrakk> \<Longrightarrow> (x \<otimes> y) \<otimes> z = x \<otimes> (y \<otimes> z)"
  assumes M4: "\<one> \<in> F \<and> \<one> \<noteq> \<zero> \<and> (\<forall> x \<in> F. \<one> \<otimes> x = x)"
  assumes M5: "\<And> x. \<lbrakk>x \<in> F; x \<noteq> \<zero>\<rbrakk> \<Longrightarrow> ((x\<dieresis>) \<in> F \<and> x \<otimes> (x\<dieresis>) = \<one>)"

  assumes D: "\<And> x y z. \<lbrakk>x \<in> F; y \<in> F; z \<in> F\<rbrakk> \<Longrightarrow> x \<otimes> (y \<oplus> z) = x \<otimes> y \<oplus> x \<otimes> z"
begin

text\<open>1.14 Propozicija\<close>
proposition T1_14_a:
  assumes "x \<in> F" and "y \<in> F" and "z \<in> F" and "x \<oplus> y = x \<oplus> z"
  shows "y = z" 
proof-
  from A4 have "y = \<zero> \<oplus> y"
    by (simp add: assms(2))
  also have "\<dots> = ((\<ominus>x) \<oplus> x) \<oplus> y"
    by (simp add: A2 A5 assms(1))
  also have "\<dots> = (\<ominus>x) \<oplus> (x \<oplus> y)"
    by (simp add: A3 A5 assms(1))
  also have "\<dots> = (\<ominus>x) \<oplus> (x \<oplus> z)"
    by (simp add: assms(4))
  also have "\<dots> = ((\<ominus>x) \<oplus> x) \<oplus> z"
    by (simp add: A3 A5 assms(1))
  also have "\<dots> = \<zero> \<oplus> z"
    by (simp add: A2 A5 assms(1))
  also have "\<dots> = z"
    by (simp add: A4 assms(3))
  finally show ?thesis
    by auto
qed

proposition T1_14_b:
  assumes "x \<in> F" and "y \<in> F" and "x \<oplus> y = x"
  shows "y = \<zero>" 
  using T1_14_a
  by (metis A2 A4 assms(1) assms(2) assms(3))

proposition T1_14_c:
  assumes "x \<in> F" and "y \<in> F" and "x \<oplus> y = \<zero>"
  shows "y = \<ominus>x" 
  using T1_14_a
  using A5 assms(1) assms(2) assms(3) by blast

proposition T1_14_d:
  assumes "x \<in> F"
  shows "(\<ominus>(\<ominus> x)) = x" 
  using T1_14_c
  using A2 A5 assms by presburger

text\<open>1.15 Propozicija\<close>
proposition T1_15_a:
  assumes "x \<in> F" and "y \<in> F" and "z \<in> F" and "x \<noteq> \<zero>" and  "x \<otimes> y = x \<otimes> z"
  shows "y = z"
  by (metis M2 M3 M4 M5 assms(1) assms(2) assms(3) assms(4) assms(5))

proposition T1_15_b:
  assumes "x \<in> F" and "y \<in> F" and "x \<noteq> \<zero>" and  "x \<otimes> y = x"
  shows "y = \<one>"
  by (metis M2 M4 T1_15_a assms(1) assms(2) assms(3) assms(4))
  
proposition T1_15_c:
  assumes "x \<in> F" and "y \<in> F" and "x \<noteq> \<zero>" and  "x \<otimes> y = \<one>"
  shows "y = (x\<dieresis>)"
  using M5 T1_15_a assms(1) assms(2) assms(3) assms(4) by presburger

proposition T1_15_d:
  assumes "x \<in> F" and "x \<noteq> \<zero>" 
  shows "((x\<dieresis>)\<dieresis>) = x"
  by (metis A2 A4 D M2 M4 M5 T1_14_a T1_15_c assms(1) assms(2))

text\<open>1.16 Propozicija\<close>
proposition T1_16_a:
  assumes "x \<in> F"
  shows "\<zero> \<otimes> x = \<zero>"
proof-
  have 1: "\<zero> \<otimes> x \<oplus> \<zero> \<otimes> x = (\<zero> \<oplus> \<zero>) \<otimes> x" 
    by (metis A4 D Polje.M2 Polje_axioms assms)
  have 2: "(\<zero> \<oplus> \<zero>) \<otimes> x = \<zero> \<otimes> x"
    by (simp add: A4)
  from this 1 have "\<zero> \<otimes> x \<oplus> \<zero> \<otimes> x = \<zero> \<otimes> x" by auto
  from this show "\<zero> \<otimes> x = \<zero>" 
    using T1_14_b
    by (meson A4 M1 assms)
qed

proposition T1_16_b:
  assumes "x \<in> F" and "y \<in> F" and "x \<noteq> \<zero>" and "y \<noteq> \<zero>"
  shows "x \<otimes> y \<noteq> \<zero>"
proof (rule ccontr)
  assume "\<not> (x \<otimes> y \<noteq> \<zero>)"
  from this have "\<one> = (y\<dieresis>) \<otimes> (x\<dieresis>) \<otimes> x \<otimes> y" 
    by (metis A4 Polje.M2 Polje_axioms T1_15_a T1_16_a assms(1) assms(2) assms(3) assms(4))
  from this have "\<one> = (y\<dieresis>) \<otimes> (x\<dieresis>) \<otimes> \<zero>" 
    using M1 M3 M5 \<open>\<not> x \<otimes> y \<noteq> \<zero>\<close> assms(1) assms(2) assms(3) assms(4) by presburger
  from this have "\<one> = \<zero>" 
    using T1_16_a 
    using A4 M1 M2 M5 assms(1) assms(2) assms(3) assms(4) by presburger
  from this show False 
    by (simp add: M4)
qed

proposition T1_16_c1:
  assumes "x \<in> F" and "y \<in> F"
  shows "(\<ominus> x) \<otimes> y = \<ominus> (x \<otimes> y)" 
proof-
  have "(\<ominus> x) \<otimes> y \<oplus> x \<otimes> y = ((\<ominus> x) \<oplus> x) \<otimes> y" 
    by (simp add: A1 A5 D M2 assms(1) assms(2))
  from this have "(\<ominus> x) \<otimes> y \<oplus> x \<otimes> y = \<zero> \<otimes> y" 
    using A2 A5 assms(1) by presburger
  from this have "(\<ominus> x) \<otimes> y \<oplus> x \<otimes> y = \<zero>"
    using T1_16_a assms(2) by auto 
  from this show ?thesis using T1_14_c 
    by (simp add: A2 A5 M1 assms(1) assms(2))
qed

proposition T1_16_c2:
  assumes "x \<in> F" and "y \<in> F"
  shows "(\<ominus> (x \<otimes> y)) = x \<otimes> (\<ominus> y)"
  using A5 M2 T1_16_c1 assms(1) assms(2) by presburger

proposition T1_16_d:
  assumes "x \<in> F" and "y \<in> F"
  shows "(\<ominus> x) \<otimes> (\<ominus> y) = x \<otimes> y"
proof-
  have "(\<ominus> x) \<otimes> (\<ominus> y) = \<ominus>(x \<otimes> (\<ominus>y))" 
    by (simp add: A5 T1_16_c1 assms(1) assms(2))
  also have "... = \<ominus>(\<ominus>(x \<otimes> y))" 
    using T1_16_c2 assms(1) assms(2) by presburger
  also have "\<dots> = x \<otimes> y" 
    by (simp add: M1 T1_14_d assms(1) assms(2))
  finally show ?thesis by auto
qed

end

text\<open>1.17 Definicija\<close>
locale Uredjeno_polje = Polje + uredjen_skup +
  assumes O1: "S = F"
  assumes O2: "\<And> x y z. \<lbrakk>x \<in> F; y \<in> F; z \<in> F; y \<prec> z\<rbrakk> \<Longrightarrow> x \<oplus> y \<prec> x \<oplus> z"
  assumes O3: "\<And> x y. \<lbrakk>x \<in> F; y \<in> F; \<zero> \<prec> x; \<zero> \<prec> y\<rbrakk> \<Longrightarrow> \<zero> \<prec> x \<otimes> y"
begin

text\<open>1.18 Propozicija\<close>
proposition T1_18_a: 
  assumes "x \<in> F"
  shows "\<zero> \<prec> x \<longleftrightarrow> (\<ominus> x) \<prec> \<zero>"
proof
  assume "\<zero> \<prec> x"
  have "\<zero> = (\<ominus> x) \<oplus> x" 
    using A2 A5 assms by blast
  from this \<open>\<zero> \<prec> x\<close> have "((\<ominus> x) \<oplus> \<zero>) \<prec> (\<ominus> x) \<oplus> x"
    using O2
    apply auto 
    using A4 A5 assms by presburger
  from this show "(\<ominus> x) \<prec> \<zero>"
    by (simp add: A2 A4 A5 assms)
next
  assume "(\<ominus> x) \<prec> \<zero>"
  show "\<zero> \<prec> x"
  proof(rule ccontr)
    assume "\<not> \<zero> \<prec> x"
    have "\<zero> = (\<ominus> x) \<oplus> x" 
      using A2 A5 assms by blast
    from this \<open>(\<ominus> x) \<prec> \<zero>\<close> \<open>\<not> \<zero> \<prec> x\<close> have "(\<ominus> x) \<oplus> x \<prec> ((\<ominus> x) \<oplus> \<zero>)"
      by (metis A4 A5 O2 Polje.A2 Polje_axioms assms)
    from this have "\<zero> \<prec> (\<ominus> x)" 
      by (metis A4 A5 Polje.A2 Polje_axioms assms)
    from this \<open>(\<ominus> x) \<prec> \<zero>\<close> show False
      by (metis A4 A5 O2 Polje.A2 Polje_axioms \<open>\<not> \<zero> \<prec> x\<close> assms)
  qed
qed

proposition T1_18_b: 
  assumes "x \<in> S" "y \<in> S" "z \<in> S" "\<zero> \<prec> x" "y \<prec> z"
  shows "x \<otimes> y \<prec> x \<otimes> z"
proof-
  from assms(5) have "y \<oplus> (\<ominus> y) \<prec> z \<oplus> (\<ominus>y)" 
    by (metis A2 A5 O1 O2 assms(2) assms(3)) 
  from this have "\<zero> \<prec> z \<oplus> (\<ominus>y)" 
    using A5 O1 assms(2) by blast
  from this have "\<zero> \<prec> x \<otimes> (z \<oplus> (\<ominus> y))" 
    using assms(4) O3 A1 A5 O1 assms(1) assms(2) assms(3) by presburger

  have "x \<otimes> y = \<zero> \<oplus> x \<otimes> y" 
    using A4 M1 O1 assms(1) assms(2) by force 
  also have "... \<prec> x \<otimes> (z \<oplus> (\<ominus> y)) \<oplus> x \<otimes> y" using \<open>\<zero> \<prec> x \<otimes> (z \<oplus> (\<ominus> y))\<close>
    by (metis A1 A2 A5 M1 O1 O2 assms(1) assms(2) assms(3))
  also have "... = x \<otimes> z \<oplus> x \<otimes> (\<ominus>y) \<oplus> x \<otimes> y" 
    using A5 D O1 assms(1) assms(2) assms(3) by presburger
  also have "... = x \<otimes> z \<oplus> \<zero>"
    by (metis A2 A3 A4 A5 D M1 O1 assms(1) assms(2) assms(3))
  also have "... = x \<otimes> z" 
    using A2 A4 M1 O1 assms(1) assms(3) by auto
  finally show ?thesis
    by simp 
qed

lemma L1_18_c_pom:
  assumes "a \<in> F" and "b \<in> F"
  shows "a \<oplus> (\<ominus>b) \<prec> \<zero> \<longrightarrow> a \<prec> b"
  by (smt (verit, ccfv_threshold) A1 A2 A5 O1 O2 assms(1) assms(2) potpunost tacno_jedan_def)


proposition T1_18_c: 
  assumes "x \<in> S" "y \<in> S" "z \<in> S" "x \<prec> \<zero>" "y \<prec> z"
  shows "x \<otimes> z \<prec> x \<otimes> y"
proof-
  have 1:"\<zero> \<prec> (\<ominus>x) \<otimes> (z \<oplus> (\<ominus>y))"
    using T1_18_a T1_18_b T1_16_c1 T1_16_c2 assms
    apply auto
    by (metis A1 A2 A5 O1 O2 O3 T1_14_d)
  then have "\<dots> = (\<ominus>(x \<otimes> (z \<oplus> (\<ominus>y))))"
    using T1_18_a T1_18_b T1_16_c1 T1_16_c2
    using A1 A5 O1 assms(1) assms(2) assms(3) by presburger
  from this 1 have "(x \<otimes> (z \<oplus> (\<ominus>y))) \<prec> \<zero>"
    using A1 A5 M1 O1 T1_14_d T1_18_a assms(1) assms(2) assms(3) by force
  then have "(x \<otimes> z) \<oplus> (x \<otimes> (\<ominus>y)) \<prec> \<zero>"
    using A5 D O1 assms(1) assms(2) assms(3) by force
  then have "(x \<otimes> z) \<oplus> (\<ominus>(x \<otimes> y)) \<prec> \<zero>"
    using O1 Polje.T1_16_c2 Polje_axioms assms(1) assms(2) by fastforce
  then show ?thesis
    using T1_18_a O1 O2 O3
    using M1 L1_18_c_pom assms(1) assms(2) assms(3) by presburger
qed

proposition T1_18_d1:
  assumes "x \<in> S" "x \<noteq> \<zero>"
  shows "\<zero> \<prec> x \<otimes> x"
proof (cases "\<zero> \<prec> x")
  case True
  then show ?thesis
    using O1 O3 assms(1) by blast
next
  case False
  then have "x \<prec> \<zero>"
    using A4 O1 assms(1) assms(2) potpunost tacno_jedan_def by auto
  then have "\<zero> \<prec> (\<ominus>x)"
    using A5 O1 T1_14_d T1_18_a assms(1) by presburger
  then have "\<zero> \<prec> (\<ominus>x) \<otimes> (\<ominus>x)"
    using A5 O1 O3 assms(1) by blast
  have "(\<ominus>x) \<otimes> (\<ominus>x) = x \<otimes> x"
    using O1 T1_16_d assms(1) by auto
  from this \<open>\<zero> \<prec> (\<ominus>x) \<otimes> (\<ominus>x)\<close> show ?thesis
    by simp
qed

proposition T1_18_d2: 
  shows "\<one> \<succ> \<zero>"
  by (metis A4 M4 O1 T1_18_d1 manje_jednako_def tacno_jedan_def uredjen_skup.potpunost uredjen_skup_axioms vece_def)

proposition T1_18_e: 
  assumes "x \<in> S" "y \<in> S" "\<zero> \<prec> x" "x \<prec> y"
  shows "(\<zero> \<prec> (y\<dieresis>)) \<and> ((y\<dieresis>) \<prec> (x\<dieresis>))"
proof-
  have "\<zero> \<prec> y"
    using A4 O1 assms(1) assms(2) assms(3) assms(4) tranzitivnost by blast
  then have 1: "\<And> v. v \<in> S \<and> v \<preceq> \<zero> \<longrightarrow> y \<otimes> v \<preceq> \<zero>"
    by (metis A4 M2 O1 T1_16_a T1_18_b assms(2) manje_jednako_def)
  have "y \<otimes> (y\<dieresis>) = \<one>"
    by (metis M5 O1 \<open>\<zero> \<prec> y\<close> assms(2) tacno_jedan_def uredjen_skup.potpunost uredjen_skup_axioms)
  have "\<zero> \<prec> \<one>"
    using M4 O1 T1_18_d1 by fastforce
  from 1 \<open>y \<otimes> (y\<dieresis>) = \<one>\<close> \<open>\<zero> \<prec> \<one>\<close> have "\<zero> \<prec> (y\<dieresis>)"
    by (smt (verit) A4 M4 M5 O1 Polje.M3 Polje_axioms T1_16_a assms(2) manje_jednako_def potpunost tacno_jedan_def)
  
  have 2: "\<And> v. v \<in> S \<and> v \<preceq> \<zero> \<longrightarrow> x \<otimes> v \<preceq> \<zero>"
    by (metis A4 M2 O1 T1_16_a T1_18_c assms(1) assms(3) manje_jednako_def)
  have "x \<otimes> (x\<dieresis>) = \<one>"
    by (metis M5 O1 assms(1) assms(3) tacno_jedan_def uredjen_skup.potpunost uredjen_skup_axioms)
  from 1 \<open>x \<otimes> (x\<dieresis>) = \<one>\<close> \<open>\<zero> \<prec> \<one>\<close> have "\<zero> \<prec> (x\<dieresis>)"
    by (smt (verit, ccfv_SIG) "2" A4 M4 M5 O1 Polje.M3 Polje_axioms T1_16_a assms(1) manje_jednako_def potpunost tacno_jedan_def)
  have mn1: "x \<otimes> ((x\<dieresis>) \<otimes> (y\<dieresis>)) = (y\<dieresis>)"
    by (smt (verit, best) O1 Polje.M3 Polje.M5 Polje_axioms Polje_def \<open>\<zero> \<prec> y\<close> assms(1) assms(2) assms(3) tacno_jedan_def uredjen_skup.potpunost uredjen_skup_axioms)
  have 3: "y \<otimes> ((y\<dieresis>) \<otimes> (x\<dieresis>)) = y \<otimes> ((x\<dieresis>) \<otimes> (y\<dieresis>))"
    by (metis O1 Polje.M2 Polje.M5 Polje_axioms \<open>\<zero> \<prec> y\<close> assms(1) assms(2) assms(3) tacno_jedan_def uredjen_skup.potpunost uredjen_skup_axioms)
  have "y \<otimes> ((y\<dieresis>) \<otimes> (x\<dieresis>)) = (x\<dieresis>)"
    by (smt (verit, best) M3 M5 O1 Polje_axioms Polje_def \<open>\<zero> \<prec> y\<close> assms(1) assms(2) assms(3) tacno_jedan_def uredjen_skup.potpunost uredjen_skup_axioms)
  from this 3 have mn2: "y \<otimes> ((x\<dieresis>) \<otimes> (y\<dieresis>)) = (x\<dieresis>)" 
    by auto
  from \<open>x \<prec> y\<close> \<open>\<zero> \<prec> (x\<dieresis>)\<close> \<open>\<zero> \<prec> (y\<dieresis>)\<close> mn1 mn2 show ?thesis
    by (smt (verit, best) O1 Polje.M1 Polje.M2 Polje.M5 Polje_axioms Uredjeno_polje.O3 Uredjeno_polje.T1_18_b Uredjeno_polje_axioms assms(1) assms(2) assms(3) tacno_jedan_def uredjen_skup.potpunost uredjen_skup_axioms) 
qed
end

global_interpretation Uredjeno_polje_test: Uredjeno_polje where
  manje = "less::(rat \<Rightarrow> rat \<Rightarrow> bool)" and
  S = "UNIV :: rat set" and
  F = "UNIV :: rat set" and
  plus = "(+)" and
  puta = "(*)" and
  nula = 0 and
  jedan = 1 and
  inverz_plus = uminus and
  inverz_puta = inverse
defines 
  uredjen_skup_vece = "uredjen_skup.vece less::(rat \<Rightarrow> rat \<Rightarrow> bool)"
  unfolding Uredjeno_polje_def uredjen_skup_def Polje_def tacno_jedan_def Uredjeno_polje_axioms_def uredjen_skup.vece_def uredjen_skup.manje_jednako_def 
  apply auto
   apply (simp add: ring_class.ring_distribs(1))
  sorry

definition potpolje where 
  "potpolje Q plus\<^sub>q puta\<^sub>q nula\<^sub>q jedan\<^sub>q inverz_plus\<^sub>q inverz_puta\<^sub>q manje\<^sub>q
            R plus\<^sub>r puta\<^sub>r nula\<^sub>r jedan\<^sub>r inverz_plus\<^sub>r inverz_puta\<^sub>r manje\<^sub>r
    \<longleftrightarrow> (Uredjeno_polje R plus\<^sub>r puta\<^sub>r nula\<^sub>r jedan\<^sub>r inverz_plus\<^sub>r inverz_puta\<^sub>r manje\<^sub>r R) \<and>
        (Uredjeno_polje Q plus\<^sub>q puta\<^sub>q nula\<^sub>q jedan\<^sub>q inverz_plus\<^sub>q inverz_puta\<^sub>q manje\<^sub>q Q) \<and>
        (\<exists> f. f` Q \<subseteq> R \<and> inj f \<and>
         (\<forall> x y. (x \<in> Q \<and> y \<in> Q) \<longrightarrow> ((puta\<^sub>r (f x) (f y)) = (f (puta\<^sub>q x y)))) \<and>
         (\<forall> x y. (x \<in> Q \<and> y \<in> Q) \<longrightarrow> ((plus\<^sub>r (f x) (f y)) = (f (plus\<^sub>q x y)))) \<and>
         (\<forall> x \<in> Q. (manje\<^sub>q nula\<^sub>q x) \<longrightarrow> (manje\<^sub>r nula\<^sub>r (f x))))"

section\<open>Polje Realnih brojeva\<close>
text\<open>1.19 Teorema\<close>
theorem T1_19:
  "\<exists> R. (Uredjeno_polje R (+) (*) 0 1 uminus inverse (<) R) \<and>
        (uredjen_skup.ima_najmanju_gornju_granicu (<) R) \<and>
        (potpolje (UNIV :: rat set) (+) (*) 0 1 uminus inverse (<)
                  R                 (+) (*) 0 1 uminus inverse (<))"
  sorry

text\<open>Da li treba da definišemo svoj tip realnih brojeva?\<close>
definition skup_realnih_brojeva :: "real set \<Rightarrow> bool"  where
"skup_realnih_brojeva R \<longleftrightarrow>  (Uredjeno_polje R (+) (*) 0 1 uminus inverse (<) R) \<and>
                            (uredjen_skup.ima_najmanju_gornju_granicu (<) R) \<and>
                            (potpolje (UNIV :: rat set) (+) (*) 0 1 uminus inverse (<)
                                      R                 (+) (*) 0 1 uminus inverse (<)) "


text\<open>1.20 Teorema\<close>
theorem T1_20_a:
  assumes "skup_realnih_brojeva R" and "x \<in> R" and "y \<in> R" and "x > 0"
  shows "\<exists> n::nat. (of_rat (of_nat n)) * x > y"
  using [[show_types]]
proof(rule ccontr)
  assume p1: " \<nexists>n::nat. y < real_of_rat (rat_of_nat n) * x"
  obtain A where "A = {a. a = real_of_rat (rat_of_nat n) * x \<and> n > 0}"
    by auto
  from this p1 have "uredjen_skup.gornja_granica less R y A" 
    by (simp add: assms(4) reals_Archimedean3)
  obtain \<alpha> where "uredjen_skup.supremum less R \<alpha> A" 
    using assms(4) p1 reals_Archimedean3 by auto

  from assms(4) have "\<alpha> - x < \<alpha>" by auto
  from this have "\<not> (uredjen_skup.gornja_granica less R (\<alpha> - x) A)"
    using ex_less_of_nat_mult p1 by auto
  from this obtain m where "m > 0 \<and> \<alpha> - x < real_of_rat (rat_of_nat m)*x"
    using assms(4) ex_less_of_nat_mult p1 by auto
  from this have "real_of_rat (rat_of_nat (m+1))*x \<in> A" "\<alpha> < real_of_rat (rat_of_nat (m+1))*x" 
    using assms(4) p1 reals_Archimedean3 apply auto[1] 
    using assms(4) ex_less_of_nat_mult p1 by auto
  from this \<open>uredjen_skup.supremum less R \<alpha> A\<close> show False
    using assms(4) p1 reals_Archimedean3 by auto
qed

theorem T1_20_b: 
  assumes "skup_realnih_brojeva R" and "x \<in> R" and "y \<in> R" and "x < y"
  shows "\<exists> p::rat. x < (of_rat p) \<and> (of_rat p) < y"
proof-
  from assms(4) have "y - x > 0" by auto
  from this obtain n::nat where "n > 0" and "n * (y - x) > 1" using T1_20_a 
    by (metis ex_less_of_nat_mult mult_eq_0_iff not_one_less_zero of_nat_0_eq_iff zero_less_iff_neq_zero)
  obtain m1::int where "m1 > 0 \<and> m1 > real_of_rat (rat_of_nat n) * x" using T1_20_a [show_types]
    by (smt (verit, del_insts) ex_less_of_int of_int_less_1_iff)
  obtain m2::int where "m2 > 0 \<and> m2 > - real_of_rat (rat_of_nat n) * x" using T1_20_a [show_types]
    by (metis ex_less_of_int le_less_trans linorder_not_le not_one_less_zero of_int_less_iff zero_less_one)
  from this have "-m2 < real_of_rat (rat_of_nat n) * x" and " real_of_rat (rat_of_nat n) * x < m1" 
    apply force
    using \<open>0 < m1 \<and> real_of_rat (rat_of_nat n) * x < real_of_int m1\<close> by auto
  from this obtain m::int where "m-1 \<le> real_of_rat (rat_of_nat n) * x" and "real_of_rat (rat_of_nat n) * x < m"
    sorry
  from this have "-m2 \<le> m" and "m < m1" 
    using \<open>real_of_int (- m2) < real_of_rat (rat_of_nat n) * x\<close> apply linarith
    sorry
  from this have "real_of_rat (rat_of_nat n) * x < m" and "m \<le> real_of_rat (rat_of_nat n) * x + 1"
    using \<open>real_of_rat (rat_of_nat n) * x < real_of_int m\<close> apply blast
    using \<open>real_of_int (m - 1) \<le> real_of_rat (rat_of_nat n) * x\<close> by linarith
  from this have " real_of_rat (rat_of_nat n) * x + 1 <  real_of_rat (rat_of_nat n) * y"
    by (smt (verit, ccfv_SIG) \<open>1 < real n * (y - x)\<close> distrib_left of_rat_of_nat_eq)
  from this \<open>n > 0\<close> have "x < m / n" 
    by (metis Groups.mult_ac(2) \<open>real_of_rat (rat_of_nat n) * x < real_of_int m\<close> mult_imp_less_div_pos of_nat_0_less_iff of_rat_of_nat_eq)
  from this \<open>n > 0\<close> \<open>y - x > 0\<close> have "m / n < y"
    by (metis \<open>real_of_int m \<le> real_of_rat (rat_of_nat n) * x + 1\<close> \<open>real_of_rat (rat_of_nat n) * x + 1 < real_of_rat (rat_of_nat n) * y\<close> le_less_trans mult.commute mult_imp_div_pos_less of_nat_0_less_iff of_rat_of_nat_eq)
  from this obtain p where "p = m/n" by auto
  from this \<open>x < m / n\<close> \<open>m / n < y\<close> have "x < p" and "p < y" by auto
  from this show ?thesis
    using assms(4) of_rat_dense by blast
qed

text\<open>1.21 Teorema\<close>
theorem T1_21:
  fixes n::nat
  assumes "skup_realnih_brojeva R" and "x \<in> R" and "x > 0" and "n > 0"
  shows "(\<exists> y \<in> R. y^n = x \<and> (\<forall> z \<in> R. z^n = x \<longrightarrow> z = y))"
  sorry

end










