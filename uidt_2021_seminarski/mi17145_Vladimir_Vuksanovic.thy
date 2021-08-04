theory mi17145_Vladimir_Vuksanovic
  imports Complex_Main
begin

text \<open>
Link: https://www.imo-official.org/problems/IMO2006SL.pdf

A2. Zadat je niz realnih brojeva [a_0, a_1, ...] definisan rekurzivno jednacinama
a_0 = -1
\<Sum> k=0..n. a_(n-k) / (k+1) = 0 za n\<ge>1

Pokazati da je a_n > 0 za n \<ge> 1.
\<close>

(* Definisanje niza *)
fun seq :: "nat \<Rightarrow> real" where
"seq 0 = -1" |
"seq n = - (\<Sum> k::nat=1..n. (seq (n-k) / (k+1)))"

value "seq 0"
value "seq 1"

(* Definicija niza zadovoljava definiciju iz zadatka *)
lemma seq_constraint:
  fixes n :: "nat"
  assumes "n \<ge> 1"
  shows "(\<Sum> k=0..n. (seq (n-k))/(k+1)) = 0"
proof-
  have "(\<Sum> k::nat=1..n. (seq (n-k) / (k+1))) + seq n = 0"
    by (smt (verit) assms not_one_le_zero seq.elims sum.cong)
  then show "(\<Sum> k::nat=0..n. (seq (n-k) / (k+1))) = 0"
    by (simp add: sum.atLeast_Suc_atMost)
qed

(* Glavna teorema zadatka *)
theorem
  fixes n :: nat
  assumes "n \<ge> 1"
  shows "(seq n) > 0"
  using assms
proof (induction n rule: nat_less_induct)
  case (1 n)
  then show ?case
    sorry
qed

(* Alternativna postavka *)
(*
theorem
  fixes n :: "nat"
  fixes seq :: "nat \<Rightarrow> real"
  assumes "seq 0 = -1"
  assumes "\<forall>n\<ge>1. (\<Sum> k=0..n. (seq (n-k))/(k+1)) = 0"
  assumes "n \<ge> 1"
  shows "seq n > 0"
  sorry
*)

end