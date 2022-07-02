theory mi18030_Isidora_Slavkovic_mi18006_Slobodan_Jenko
  imports Main HOL.Rat
begin

text\<open>https://web.math.ucsb.edu/~agboola/teaching/2021/winter/122A/rudin.pdf\<close>

definition tacno_jedan :: "bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool"  where
  "tacno_jedan a b c \<longleftrightarrow> (a \<or> b \<or> c) \<and> (\<not>a \<or> \<not>b) \<and> (\<not>a \<or> \<not>c) \<and> (\<not>b \<or> \<not>c)"

section\<open>Uredjeni Skupovi\<close>

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
  fixes nula :: "'a"
  fixes jedan :: "'a"
  fixes inverz_plus :: "'a \<Rightarrow> 'a"
  fixes inverz_puta :: "'a \<Rightarrow> 'a"

  assumes A1: "\<And> x y. \<lbrakk>x \<in> F; y \<in> F\<rbrakk> \<Longrightarrow> x \<oplus> y \<in> F"
  assumes A2: "\<And> x y. \<lbrakk>x \<in> F; y \<in> F\<rbrakk> \<Longrightarrow> x \<oplus> y = y \<oplus> x"
  assumes A3: "\<And> x y. \<lbrakk>x \<in> F; y \<in> F\<rbrakk> \<Longrightarrow> (x \<oplus> y) \<oplus> z = x \<oplus> (y \<oplus> z)"
  assumes A4: "nula \<in> F \<and> (\<forall> x \<in> F. nula \<oplus> x = x)"
  assumes A5: "\<And> x. \<lbrakk>x \<in> F\<rbrakk> \<Longrightarrow> (inverz_plus x) \<in> F \<and> x \<oplus> (inverz_plus x) = nula"

  assumes M1: "\<And> x y. \<lbrakk>x \<in> F; y \<in> F\<rbrakk> \<Longrightarrow> x \<otimes> y \<in> F"
  assumes M2: "\<And> x y. \<lbrakk>x \<in> F; y \<in> F\<rbrakk> \<Longrightarrow> x \<otimes> y = y \<otimes> x"
  assumes M3: "\<And> x y. \<lbrakk>x \<in> F; y \<in> F\<rbrakk> \<Longrightarrow> (x \<otimes> y) \<otimes> z = x \<otimes> (y \<otimes> z)"
  assumes M4: "jedan \<in> F \<and> jedan \<noteq> nula \<and> (\<forall> x \<in> F. jedan \<otimes> x = x)"
  assumes M5: "\<And> x. \<lbrakk>x \<in> F; x \<noteq> nula \<rbrakk> \<Longrightarrow> (inverz_puta x \<in> F \<and> x \<otimes> (inverz_puta x) = jedan)"

  assumes D: "\<And> x y z. \<lbrakk>x \<in> F; y \<in> F; z \<in> F\<rbrakk> \<Longrightarrow> x \<otimes> (y \<oplus> z) = x \<otimes> y \<oplus> x \<otimes> z"
begin

text\<open>1.14 Propozicija\<close>
proposition 
  assumes "x \<oplus> y = x \<oplus> z"
  shows "y = z" 
  sorry
proposition 
  assumes "x \<oplus> y = x"
  shows "y = nula" 
  sorry
proposition 
  assumes "x \<oplus> y = nula"
  shows "y = inverz_plus x" 
  sorry
proposition 
  shows "inverz_plus (inverz_plus x) = x" 
  sorry

text\<open>1.15 Propozicija\<close>
proposition 
  assumes "x \<noteq> nula" and  "x \<otimes> y = x \<otimes> z"
  shows "y = z"
  sorry
proposition 
  assumes "x \<noteq> nula" and  "x \<otimes> y = x"
  shows "y = jedan"
  sorry
proposition 
  assumes "x \<noteq> nula" and  "x \<otimes> y = jedan"
  shows "y = inverz_puta x"
  sorry
proposition 
  assumes "x \<noteq> nula" 
  shows "inverz_puta (inverz_puta x) = x"
  sorry

text\<open>1.16 Propozicija\<close>
proposition "nula \<otimes> x = nula"
  sorry
proposition 
  assumes "x \<noteq> nula" and "y \<noteq> nula"
  shows "x \<otimes> y \<noteq> nula"
  sorry
proposition "(inverz_plus x) \<otimes> y = x \<otimes> (inverz_plus y)"
  sorry
proposition "(inverz_plus x) \<otimes> (inverz_plus y) = x \<otimes> y"
  sorry

end

(*
locale Uredjenje =
  fixes uredjenje :: "'a rel"
  fixes manje_fun :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infixl "\<prec>" 101) where 
    "x \<prec> y \<longleftrightarrow> (x,y) \<in> uredjenje"
  assumes potpunost: "tacno_jedan (x \<prec> y) (x = y) (y \<prec> x)"
  assumes tranzitivnost: "\<lbrakk>x \<prec> y; y \<prec> z\<rbrakk> \<Longrightarrow> x \<prec> z"
begin
definition manje_jednako :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infixl "\<preceq>" 102) where
  "x \<preceq> y \<longleftrightarrow> x \<prec> y \<or> x = y"

type_synonym uredjen_skup = "('a set) \<times> ('a rel)"

end
*)

end

