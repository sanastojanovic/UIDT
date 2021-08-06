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

find_theorems "_ * (_ + _)"
find_theorems "_ * sum _ _"
find_theorems "sum _ _ - sum _ _"
find_theorems "_ - _ + _ = _ + _ - _"

find_theorems "sum _ _ = _ + sum _ _"
thm "sum.atLeast_Suc_atMost"

find_theorems "0 < sum _ _"
thm "sum_pos"

find_theorems "-sum _ _"

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

    then have "(n+1) * ((seq n / (n-n+1)) + (\<Sum> k=0..n-1. (seq k)/(n-k+1))) - (n)*(\<Sum> k=0..n-1. (seq k)/(n-k)) = 0"
      by (smt (verit) Nat.add_diff_assoc2 1 Suc_eq_plus1 add_diff_cancel_right' sum.atLeast0_atMost_Suc)

    then have "(n+1) * ((seq n) + (\<Sum> k=0..n-1. (seq k)/(n-k+1))) - (n)*(\<Sum> k=0..n-1. (seq k)/(n-k)) = 0"
      by simp

    then have "((n+1) * (seq n) + (n+1) * ((\<Sum> k=0..n-1. (seq k)/(n-k+1)))) - (n)*(\<Sum> k=0..n-1. (seq k)/(n-k)) = 0"
      by (simp add: algebra_simps)

    then have "(n+1) * (seq n) + (\<Sum> k=0..n-1. (n+1)*(seq k)/(n-k+1)) - (\<Sum> k=0..n-1. (n)*(seq k)/(n-k)) = 0"
      by (simp add: sum_distrib_left)

    then have "(n+1) * (seq n) + (\<Sum> k=0..n-1. (n+1)*(seq k)/(n-k+1) - (n)*(seq k)/(n-k)) = 0"
      by (simp add:  sum_subtractf)

    then have "(n+1) * (seq n) + (\<Sum> k=0..n-1. ((n+1)/(n-k+1) - n/(n-k))*(seq k)) = 0"
      by (simp add: algebra_simps)

    then have "(n+1) * (seq n) =  -1 * (\<Sum> k=0..n-1. ((n+1)/(n-k+1) - n/(n-k))*(seq k))"
      by linarith

    then have "(n+1) * (seq n) =  -1 * (\<Sum> k=1..n-1. ((n+1)/(n-k+1) - n/(n-k))*(seq k))"
      using \<open>n > 1\<close>
      by (auto simp add: sum.atLeast_Suc_atMost)

    then have "(n+1) * (seq n) =  (\<Sum> k=1..n-1. -1 * ((n+1)/(n-k+1) - n/(n-k))*(seq k))"
      by (auto simp add: algebra_simps sum_distrib_left)

    also have "\<dots> > 0"
    proof (rule sum_pos)
      show "finite {1..n - 1}"
        by simp
    next
      show "{1..n - 1} \<noteq> {}"
        using \<open>n>1\<close>
        by simp
    next
      fix i
      assume "i \<in> {1..n - 1}"
      have *: "seq i > 0"
        using \<open>i \<in> {1..n - 1}\<close> 1
        by auto
      have "- 1 * ((n + 1) / (n - i + 1) - n / (n - i)) = (n / (n - i) - (n + 1) / (n - i + 1))"        
        by (auto simp add: field_simps)
      also have "... = (n*(n - i + 1))/((n - i)*(n - i + 1)) - ((n + 1)*(n - i)) / ((n - i)*(n - i + 1))"
        using \<open>i \<in> {1..n - 1}\<close> 
        by (smt (verit, ccfv_threshold) add_is_0 atLeastAtMost_iff diff_diff_cancel diff_is_0_eq' diff_le_self diff_zero le_trans nonzero_mult_divide_mult_cancel_right nonzero_mult_divide_mult_cancel_right2 of_nat_eq_0_iff of_nat_mult one_neq_zero)
      also have "... = (n*(n - i + 1)-(n + 1)*(n - i))/((n - i)*(n - i + 1))"
        using \<open>i \<in> {1..n - 1}\<close>
        by (smt (verit) diff_divide_distrib diff_le_self distrib_left distrib_right mult_of_nat_commute nat_add_left_cancel_le nat_mult_1_right of_nat_1 of_nat_diff)
      also have "... = i / ((n - i) * (n - i + 1))"
        using \<open>i \<in> {1..n - 1}\<close>
        by (auto simp add: field_simps of_nat_diff)
      also have "... > 0"
      proof-
        have "i>0" using \<open>i \<in> {1..n - 1}\<close> by simp
        moreover
        have "((n - i) * (n - i + 1)) > 0" 
          using \<open>i \<in> {1..n - 1}\<close> by auto
        ultimately
        show ?thesis
          using \<open>i \<in> {1..n - 1}\<close> by simp
      qed
      finally show "0 < - 1 * ((n + 1) / (n - i + 1) - n / (n - i)) * seq i"
        using \<open>i \<in> {1..n - 1}\<close> *
        by simp
    qed
    finally show ?thesis using \<open>n>1\<close>
      using of_nat_less_0_iff zero_less_mult_iff by blast
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