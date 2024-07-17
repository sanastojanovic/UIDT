theory KIAA
imports Main "HOL-Number_Theory.Number_Theory"
begin

(* Author: mi21386_Stefan_Neskovic *)


(*definicije sabiranja,mnozenja i oduzimanja po modulu*)
definition add_mod :: "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int" where
"add_mod a b m = ((a mod m) + (b mod m)) mod m"

definition mult_mod :: "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int" where
"mult_mod a b m = ((a mod m) * (b mod m)) mod m"

definition sub_mod :: "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int" where
"sub_mod a b m = ((a mod m) - (b mod m) + m) mod m"

(*stepenovanje po modulu*)
fun pow_mod :: "int \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> int" where
"pow_mod a 0 m = 1" |
"pow_mod a (Suc n) m = (a * pow_mod a n m) mod m"



(*dokaz korektnosti sabiranja po modulu*)
lemma add_mod_correct:
  assumes "m \<noteq> 0"
  shows "(a + b) mod m = add_mod a b m"
  using assms unfolding add_mod_def
  by presburger

(*dokaz korektnosti mnozenja po modulu *)
lemma mult_mod_correct:
  assumes "m \<noteq> 0"
  shows "(a * b) mod m = mult_mod a b m"
  using assms unfolding mult_mod_def by (simp add: mod_mult_eq)


(*dokaz korektnosti oduzimanja po modulu*)
lemma sub_mod_correct:
  assumes "m \<noteq> 0"
  shows "(a - b) mod m = sub_mod a b m"
  using assms unfolding sub_mod_def
  by (simp add: mod_add_eq mod_diff_eq)

(*definicija uzajamno prostih brojeva*)

definition coprime :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
  "coprime a n \<longleftrightarrow> gcd a n = 1"

(*provera ispravnosti*)
value "coprime 10 3"
value "coprime 12 2"



(*definicija ojlerovog broja*)

definition euler_phi :: "nat \<Rightarrow> nat" where
  "euler_phi n = fold (\<lambda>k count. if coprime k n then count + 1 else count) [1..<Suc n] 0"

(*setio sam se ovog pristupa koristeci fold jer osnovni pristup 

definition euler_phi :: "nat \<Rightarrow> nat" where
  "euler_phi n = card {k. 1 \<le> k \<and> k \<le> n \<and> coprime k n}"

daje mnogo gresaka

*)

(*provera vrednosti ojlerovog broja*)
value "euler_phi 10"  
value "euler_phi 20"  
value "euler_phi 50"  

definition congruent :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "congruent a b m \<longleftrightarrow> (a mod m = b mod m)"

(*osnovna svojstva kongruentnosti*)
lemma congruent_0_iff: "congruent a 0 m \<longleftrightarrow> m dvd a"
  by (simp add: congruent_def dvd_eq_mod_eq_0)

(* Relacija ekvivalencije *)
lemma congruent_refl: "congruent a a m"
  by (simp add: congruent_def)


lemma congruent_sym: "congruent a b m \<Longrightarrow> congruent b a m"
  by (simp add: congruent_def)

lemma congruent_trans: "\<lbrakk> congruent a b m; congruent b c m \<rbrakk> \<Longrightarrow> congruent a c m"
  by (simp add: congruent_def)


(*Ako su c i m uzajamno prosti (važi nzd(c,m)=1), tada iz c\<cdot>a\<equiv>c\<cdot>b (mod m) 
sledi a\<equiv>b (mod m) (kongruencija se može skratiti sa c).*)

(*nece da prepozna cong a ne dozvoljava mi unfolding nad congruent koji sam ja napravio*)

lemma cong_dvd_eq_mod_eq_0:
  assumes "m dvd (a - b)"
  shows "a \<equiv> b mod m"
  using assms
  unfolding congruent_def
  oops


(* Dodatna lema za demonstraciju da m deli (a - b) ako m deli c * (a - b) i gcd(c, m) = 1 *)
lemma coprime_mult_divides:
  assumes "coprime c m" and "m dvd c * (a - b)"
  shows "m dvd (a - b)"
proof -
  from assms(1) have "gcd c m = 1" 
    by (simp add: coprime_def)
  then have "gcd m c = 1"
    by (simp add: gcd.commute)
  with assms(2) show "m dvd (a - b)"
  by (metis (no_types, opaque_lifting) dvd_triv_right gcd_mult_distrib_nat gcd_unique_nat mult.commute nat_mult_1_right)
qed

lemma cancel_coprime_congruence:
  assumes "coprime c m" and "c * a \<equiv> c * b mod m"
  shows "a \<equiv> b mod m"
proof -
  from assms(2) have "m dvd (c * a - c * b)" 
    by simp  
  then have "m dvd c * (a - b)" 
    by (simp add: algebra_simps) 
  then have "m dvd (a - b)"
    using assms(1) coprime_mult_divides by blast  
  thus show "a \<equiv> b mod m"
     by (simp add: cong_dvd_eq_mod_eq_0) (*ne prepoznaje,a neuspesno sam pokusao da napravim svoju pomocnu lemu*)
qed



(*lema 3.4.2. mnozenje po modulu*)

(* (a \<cdot> b) mod m=(a mod m \<cdot> b mod m) mod m *)

definition mod_mult_equiv :: "nat => nat => nat => bool" where
  "mod_mult_equiv a b m \<equiv> (a * b) mod m = ((a mod m) * (b mod m)) mod m"


theorem mod_mult_equiv_proof:
  assumes "a = q1 * m + r1" and "b = q2 * m + r2" and "r1 < m" and "r2 < m"
  shows "mod_mult_equiv a b m"
proof -
  from assms have "a * b = ((q1 * m + r1) * (q2 * m + r2))" by simp
  also have "... = q1 * q2 * m * m + q1 * r2 * m + r1 * q2 * m + r1 * r2" by (simp add: algebra_simps)
  finally have ab_expanded: "a * b = q1 * q2 * m * m + q1 * r2 * m + r1 * q2 * m + r1 * r2" .

  have "(a * b) mod m = ((q1 * q2 * m * m + q1 * r2 * m + r1 * q2 * m + r1 * r2) mod m)" by (simp add: ab_expanded)
  also have "... = (q1 * q2 * m * m mod m + q1 * r2 * m mod m + r1 * q2 * m mod m + r1 * r2 mod m) mod m"
  by (smt (verit, best) mod_add_cong mod_mod_trivial)
  also have "... = (0 + q1 * r2 * m mod m + r1 * q2 * m mod m + r1 * r2 mod m) mod m"
  by auto
  also have "... = (q1 * r2 * m mod m + r1 * q2 * m mod m + r1 * r2) mod m"
    by simp
  also have "... = (q1 * r2 mod m * m + r1 * q2 mod m * m + r1 * r2) mod m"
  by (simp add: group_cancel.add1)
  also have "... = (q1 * r2 mod m * m + r1 * q2 mod m * m + r1 * r2 mod m) mod m"
  by (simp add: mod_add_right_eq)
  finally have ab_mod: "(a * b) mod m = ((a mod m) * (b mod m)) mod m"
    by (simp add: mod_mult_eq)

  thus ?thesis unfolding mod_mult_equiv_def by blast
qed

(*zapisi ojlerove i varijacije fermaovih teorema*)


theorem Euler:
  assumes "coprime a n"
  shows "a ^ (euler_phi n) \<equiv> 1 mod n"
  oops 


theorem Fermat_Little:
  assumes "prime p" and "coprime a p"
  shows "a ^ (p - 1) \<equiv> 1 mod p"
  oops  


theorem Fermat_Little_General:
  assumes "prime p"
  shows "a ^ p \<equiv> a mod p"
  oops  





end