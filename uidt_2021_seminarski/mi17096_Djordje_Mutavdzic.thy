theory mi17096_Djordje_Mutavdzic
  imports Complex_Main HOL.GCD
begin

text\<open>
link : https://www.imo-official.org/problems/IMO2013SL.pdf
Number theory: N3
Prove that there exist infinitely many positive integers n such that the largest prime divisor
of n^4 + n^2 + 1 is equal to the largest prime divisor of (n+1)^4+ (n+1)^2 + 1
\<close>

fun prost :: "int \<Rightarrow> bool" where
"prost x \<longleftrightarrow> (\<forall> n \<in> (set [2..(x-1)]). \<not>(n dvd x)) "

fun najveci_delilac :: "nat \<Rightarrow> nat  \<Rightarrow> bool" where
"najveci_delilac x y \<longleftrightarrow> (x dvd y) \<and> (\<forall> z \<in> (set (filter (\<lambda> k. k dvd y & prost k) [1..y])). x \<ge> z)"

fun najveci_prost_delilac :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
"najveci_prost_delilac x y \<longleftrightarrow> prost x \<and> najveci_delilac x y"

fun najveci_prost_alternativa :: "nat \<Rightarrow> int" where
"najveci_prost_alternativa x = hd(rev(filter (\<lambda> k. k dvd x & prost k) [1..x]))"

lemma
  fixes p q n :: "nat"
  assumes "najveci_prost_delilac p (n^4 + n^2 + 1)"
  assumes "najveci_prost_delilac q ((n+1)^4 + (n+1)^2 + 1)"
  shows "p == q"
  sorry



end