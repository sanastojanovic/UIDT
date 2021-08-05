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

(* Pretrazivanje teorema *)

find_theorems name: "reindex"
thm "sum.reindex_bij_witness"

(* Glavna teorema zadatka *)
theorem
  fixes n :: nat
  assumes "n \<ge> 1"
  shows "(seq n) > 0"
  using assms
proof (induction n rule: nat_less_induct)
  case (1 n)
  then show ?case
  proof (cases "n=1")
    case True
    then show ?thesis by simp
  next
    case False
    then have "n>1" using \<open>n\<ge>1\<close> by simp

    have *: "(\<Sum> k=0..n. (seq k)/(n-k+1)) = 0"
    proof-
      have "(\<Sum> k=0..n. (seq k)/(n-k+1)) = (\<Sum> k=0..n. (seq (n-k))/(k+1))"
        by (rule sum.reindex_bij_witness[of _ "\<lambda>k. n-k" "\<lambda>k. n-k"]) auto
      also have "\<dots> = 0"
        using \<open>n>1\<close>
        by (auto simp only: seq_constraint)
      finally show ?thesis
        .
    qed

    (* mora da postoji bolji nacin za ovo *)
    have **: "(\<Sum> k=0..n-1. (seq k)/(n-k)) = 0"
    proof-
      have "(\<Sum> k=0..n-1. (seq k)/(n-1-k+1)) = (\<Sum> k=0..n-1. (seq (n-1-k))/(k+1))"
        apply (rule sum.reindex_bij_witness[of _ "\<lambda>k. n-1-k" "\<lambda>k. n-1-k"])
            apply (meson atLeastAtMost_iff diff_diff_cancel)
           apply (meson atLeastAtMost_iff diff_le_self zero_le)
          apply (meson atLeastAtMost_iff diff_diff_cancel)
         apply (meson atLeastAtMost_iff diff_le_self zero_le)
        by (metis atLeastAtMost_iff diff_diff_cancel)
      also have "... = 0"
        using \<open>n>1\<close>
        by (simp only: seq_constraint)
      finally show ?thesis
        by (smt (verit, del_insts) Nat.add_diff_assoc2 1 atLeastAtMost_iff le_add_diff_inverse2 sum.cong)
    qed

    have "(n+1) * (\<Sum> k=0..n. (seq k)/(n-k+1)) - (n)*(\<Sum> k=0..n-1. (seq k)/(n-k)) = 0"
      using * **
      by simp

  qed
  
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