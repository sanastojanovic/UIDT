theory mi18030_Isidora_Slavkovic_mi18006_Slobodan_Jenko
  imports Main HOL.Rat HOL.Orderings
begin

text\<open>https://web.math.ucsb.edu/~agboola/teaching/2021/winter/122A/rudin.pdf\<close>

definition tacno_jedan :: "bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool"  where
  "tacno_jedan a b c \<longleftrightarrow> (a \<or> b \<or> c) \<and> (\<not>a \<or> \<not>b) \<and> (\<not>a \<or> \<not>c) \<and> (\<not>b \<or> \<not>c)"

section\<open>Uredjeni Skupovi\<close>

text\<open>1.6 Definicija\<close>
locale uredjen_skup =
  fixes manje :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infixl "\<prec>" 99)
  fixes S :: "'a set"
  assumes potpunost: "\<And>x y. \<lbrakk>x \<in> S; y \<in> S\<rbrakk> \<Longrightarrow>
                        tacno_jedan (x \<prec> y) (x = y) (y \<prec> x)"
  assumes tranzitivnost: "\<And>x y z. \<lbrakk>x \<in> S; y \<in> S; z \<in> S; x \<prec> y; y \<prec> z\<rbrakk> \<Longrightarrow> x \<prec> z"
begin
definition manje_jednako :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infixl "\<preceq>" 102) where
  "x \<preceq> y \<longleftrightarrow> x \<prec> y \<or> x = y"

(*type_synonym uredjen_skup = "'a set"*)
end

term "less::(nat \<Rightarrow> nat \<Rightarrow> bool)"

global_interpretation uredjen_skup where
  manje = "less::(nat \<Rightarrow> nat \<Rightarrow> bool)" and
  S = "{1,2,3,4,5::nat}"
unfolding tacno_jedan_def uredjen_skup_def
  by auto






text\<open>1.7 Definicija\<close>
definition ogranicen_odozgo where
  "ogranicen_odozgo E S \<longleftrightarrow> (E \<subset> S) \<and> (\<exists> \<beta> \<in> S. (\<forall> x \<in> E. x \<le> \<beta>))"

definition gornja_granica where
  "gornja_granica \<beta> E S \<longleftrightarrow> (E \<subset> S) \<and> (\<beta> \<in> S \<and> (\<forall> x \<in> E. x \<le> \<beta>))"

definition ogranicen_odozdo where
  "ogranicen_odozdo E S \<longleftrightarrow> (E \<subset> S) \<and> (\<exists> \<beta> \<in> S. (\<forall> x \<in> E. x \<ge> \<beta>))"

definition donja_granica where
  "donja_granica \<beta> E S \<longleftrightarrow> (E \<subset> S) \<and> (\<beta> \<in> S \<and> (\<forall> x \<in> E. x \<ge> \<beta>))"

text\<open>1.8 Definicija\<close>
definition supremum where 
  "supremum \<alpha> E S \<longleftrightarrow> (E \<subset> S) \<and> (ogranicen_odozgo E S) \<and> (\<alpha> \<in> S) \<and> 
                       (gornja_granica \<alpha> E S) \<and> 
                      (\<forall> \<gamma> \<in> E. \<gamma> < \<alpha> \<longrightarrow> \<not> (gornja_granica \<gamma> E S))"

definition infimum where
  "infimum \<alpha> E S \<longleftrightarrow> (E \<subset> S) \<and> (ogranicen_odozdo E S) \<and> (\<alpha> \<in> S) \<and> 
                       (donja_granica \<alpha> E S) \<and> 
                      (\<forall> \<gamma> \<in> E. \<gamma> > \<alpha> \<longrightarrow> \<not> (donja_granica \<gamma> E S))"

value "supremum 3 {1,2,3} {0,1,2,3,4::nat}"

value "infimum 1 {1,2,3} {0,1,2,3,4::nat}"

notation Set.empty ("\<emptyset> ")

text\<open>1.10 Definicija\<close>
definition ima_najmanju_gornju_granicu where 
  "ima_najmanju_gornju_granicu S \<longleftrightarrow> 
    (\<forall> E \<subset> S. (E \<noteq> \<emptyset>) \<and> (ogranicen_odozgo E S) \<longrightarrow> (\<exists> \<alpha> \<in> S. supremum \<alpha> E S))"

value "True < False"
value "{x. x\<in>{1,2,3,4,5::nat} \<and> x > 3}"
value "{x. x\<in>{0::nat,1,2,3,4} \<and> donja_granica x {2,3::nat} {0::nat,1,2,3,4}}"

text\<open>1.11 Teorema\<close>
theorem T1_11: 
  assumes "ima_najmanju_gornju_granicu S"
  assumes "B \<subset> S \<and> (B \<noteq> \<emptyset>) \<and> (ogranicen_odozdo B S)"
  assumes "L = {x. x \<in> S \<and>  donja_granica x B S}"
  shows "(\<exists> \<alpha> \<in> S. (supremum \<alpha> L S) \<and> (infimum \<alpha> B S))"
  sorry

section \<open>Polje\<close>

text\<open>1.12 Definicija\<close>
locale Polje =
  fixes F :: "'a set"
  fixes plus :: "'a \<Rightarrow> 'a  \<Rightarrow> 'a" (infixl "\<oplus>" 100)
  fixes puta :: "'a \<Rightarrow> 'a  \<Rightarrow> 'a" (infixl "\<otimes>" 101)
  fixes nula :: "'a" ("\<zero>")
  fixes jedan :: "'a" ("\<one>")
  fixes inverz_plus :: "'a \<Rightarrow> 'a" ("\<ominus>_" 102)
  fixes inverz_puta :: "'a \<Rightarrow> 'a" ("_\<dieresis>" 103)

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
proposition 
  assumes "x \<oplus> y = x \<oplus> z"
  shows "y = z" 
  sorry
proposition 
  assumes "x \<oplus> y = x"
  shows "y = \<zero>" 
  sorry
proposition 
  assumes "x \<oplus> y = \<zero>"
  shows "y = \<ominus>x" 
  sorry
proposition 
  shows "(\<ominus>(\<ominus> x)) = x" 
  sorry

text\<open>1.15 Propozicija\<close>
proposition 
  assumes "x \<noteq> \<zero>" and  "x \<otimes> y = x \<otimes> z"
  shows "y = z"
  sorry
proposition 
  assumes "x \<noteq> \<zero>" and  "x \<otimes> y = x"
  shows "y = \<one>"
  sorry
proposition 
  assumes "x \<noteq> \<zero>" and  "x \<otimes> y = \<one>"
  shows "y = (x\<dieresis>)"
  sorry
proposition 
  assumes "x \<noteq> \<zero>" 
  shows "((x\<dieresis>)\<dieresis>) = x"
  sorry

text\<open>1.16 Propozicija\<close>
proposition "\<zero> \<otimes> x = \<zero>"
  sorry
proposition 
  assumes "x \<noteq> \<zero>" and "y \<noteq> \<zero>"
  shows "x \<otimes> y \<noteq> \<zero>"
  sorry
proposition "(\<ominus> x) \<otimes> y = x \<otimes> (\<ominus> y)"
  sorry
proposition "(\<ominus> x) \<otimes> (\<ominus> y) = x \<otimes> y"
  sorry




end




end

