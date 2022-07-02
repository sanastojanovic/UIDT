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

