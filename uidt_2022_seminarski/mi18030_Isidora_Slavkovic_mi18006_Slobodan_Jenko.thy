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
  "ogranicen_odozgo E \<longleftrightarrow> (E \<subset> S) \<and> (\<exists> \<beta> \<in> S. (\<forall> x \<in> E. x \<preceq> \<beta>))"

definition gornja_granica where
  "gornja_granica \<beta> E \<longleftrightarrow> (E \<subset> S) \<and> (\<beta> \<in> S \<and> (\<forall> x \<in> E. x \<preceq> \<beta>))"

definition ogranicen_odozdo where
  "ogranicen_odozdo E \<longleftrightarrow> (E \<subset> S) \<and> (\<exists> \<beta> \<in> S. (\<forall> x \<in> E. x \<succeq> \<beta>))"

definition donja_granica where
  "donja_granica \<beta> E \<longleftrightarrow> (E \<subset> S) \<and> (\<beta> \<in> S \<and> (\<forall> x \<in> E. x \<succeq> \<beta>))"

text\<open>1.8 Definicija\<close>
definition supremum where 
  "supremum \<alpha> E \<longleftrightarrow> (E \<subset> S) \<and> (ogranicen_odozgo E) \<and> (\<alpha> \<in> S) \<and> 
                       (gornja_granica \<alpha> E) \<and> 
                      (\<forall> \<gamma> \<in> E. \<gamma> \<prec> \<alpha> \<longrightarrow> \<not> (gornja_granica \<gamma> E))"

definition infimum where
  "infimum \<alpha> E \<longleftrightarrow> (E \<subset> S) \<and> (ogranicen_odozdo E) \<and> (\<alpha> \<in> S) \<and> 
                       (donja_granica \<alpha> E) \<and> 
                      (\<forall> \<gamma> \<in> E. \<gamma> \<succ> \<alpha> \<longrightarrow> \<not> (donja_granica \<gamma> E))"

notation Set.empty ("\<emptyset> ")

text\<open>1.10 Definicija\<close>
definition ima_najmanju_gornju_granicu where 
  "ima_najmanju_gornju_granicu  \<longleftrightarrow> 
    (\<forall> E \<subset> S. (E \<noteq> \<emptyset>) \<and> (ogranicen_odozgo E) \<longrightarrow> (\<exists> \<alpha> \<in> S. supremum \<alpha> E))"

text\<open>1.11 Teorema\<close>
theorem T1_11: 
  assumes "ima_najmanju_gornju_granicu"
  assumes "B \<subset> S \<and> (B \<noteq> \<emptyset>) \<and> (ogranicen_odozdo B)"
  assumes "L = {x. x \<in> S \<and>  donja_granica x B}"
  shows "(\<exists> \<alpha> \<in> S. (supremum \<alpha> L) \<and> (infimum \<alpha> B))"
  sorry

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

text\<open>1.17 Definicija\<close>
locale Uredjeno_polje = Polje + uredjen_skup +
  assumes "S = F"
  assumes "\<And> x y z. \<lbrakk>x \<in> F; y \<in> F; z \<in> F; y \<prec> z\<rbrakk> \<Longrightarrow> x \<oplus> y \<prec> x \<oplus> z"
  assumes "\<And> x y. \<lbrakk>x \<in> F; y \<in> F; x \<succ> \<zero>; y \<succ> \<zero>\<rbrakk> \<Longrightarrow> x \<otimes> y \<succ> \<zero>"
begin

text\<open>1.18 Propozicija\<close>
proposition T1_18_a: 
  assumes "x \<in> F"
  shows "x \<succ> \<zero> \<longleftrightarrow> (\<ominus> x) \<prec> \<zero>"
  sorry

proposition T1_18_b: 
  assumes "x \<in> S" "y \<in> S" "z \<in> S" "x \<succ> \<zero>" "y \<prec> z"
  shows "x \<otimes> y \<prec> x \<otimes> z"
  sorry

proposition T1_18_c: 
  assumes "x \<in> S" "y \<in> S" "z \<in> S" "x \<prec> \<zero>" "y \<prec> z"
  shows "x \<otimes> y \<succ> x \<otimes> z"
  sorry

proposition T1_18_d1: 
  assumes "x \<in> S" "x \<noteq> \<zero>"
  shows "x \<otimes> x \<succ> \<zero>"
  sorry

proposition T1_18_d2: 
  shows "\<one> \<succ> \<zero>"
  sorry

proposition T1_18_e: 
  assumes "x \<in> S" "y \<in> S" "\<zero> \<prec> x" "x \<prec> y"
  shows "(\<zero> \<prec> (y\<dieresis>)) \<and> ((y\<dieresis>) \<prec> (x\<dieresis>))"
  sorry
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
        (Q \<subseteq> R) \<and>
        (\<forall> x y. (x \<in> Q \<and> y \<in> Q) \<longrightarrow> ((puta\<^sub>r x y) = (puta\<^sub>q x y))) \<and>
        (\<forall> x y. (x \<in> Q \<and> y \<in> Q) \<longrightarrow> ((plus\<^sub>r x y) = (plus\<^sub>q x y))) \<and>
        (\<forall> x \<in> Q. (manje\<^sub>q nula\<^sub>q x) \<longrightarrow> (manje\<^sub>r nula\<^sub>r x))"

section\<open>Polje Realnih brojeva\<close>
text\<open>1.19 Teorema\<close>
theorem T1_19:
  "\<exists> R. (Uredjeno_polje R (+) (*) 0 1 uminus inverse (<) R) \<and>
        (uredjen_skup.ima_najmanju_gornju_granicu (<) R) \<and>
        (potpolje (UNIV :: rat set) (+) (*) 0 1 uminus inverse (<)
                  R                 (+) (*) 0 1 uminus inverse (<))"
  sorry

definition skup_realnih_brojeva  where
"skup_realnih_brojeva R \<longleftrightarrow>  (Uredjeno_polje R (+) (*) 0 1 uminus inverse (<) R) \<and>
                            (uredjen_skup.ima_najmanju_gornju_granicu (<) R) \<and>
                            (potpolje (UNIV :: rat set) (+) (*) 0 1 uminus inverse (<)
                                      R                 (+) (*) 0 1 uminus inverse (<)) "


text\<open>1.20 Teorema\<close>
theorem T1_20_a:
  assumes "skup_realnih_brojeva R" and "x \<in> R" and "y \<in> R" and "x > 0"
  shows "\<exists> n \<in> R. n * x > y"
  sorry

theorem T1_20_b: 
  assumes "skup_realnih_brojeva R" and "x \<in> R" and "y \<in> R" 
  shows "\<exists> p \<in> (UNIV::rat set). x < p \<and> p < y"
  sorry



end










