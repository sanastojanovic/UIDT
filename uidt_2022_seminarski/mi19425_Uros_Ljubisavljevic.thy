theory mi19425_Uros_Ljubisavljevic
  imports Main
begin

text\<open>https://www.imo-official.org/problems/IMO2010SL.pdf\<close>

\<comment>\<open> Sequence definiton \<close>

fun seqX :: "nat \<Rightarrow> int" where
"seqX n = ( if (n = 0) then 0
            else if (n = 1) then 1
            else if (n mod 2 = 0) then (-seqX (n div 2))
            else ((-1)^((n + 3) div 2)) * (seqX ((n + 1) div 2)))"

value "seqX "

\<comment>\<open> S_n definition \<close>
primrec sumFst :: "nat \<Rightarrow> int" where
"sumFst 0 = 0" |
"sumFst (Suc n) = seqX (Suc n) + sumFst n"

value "sumFst 12"
value "sumFst 3"

\<comment>\<open> ======== Observations: ======= \<close>
\<comment>\<open> (1) \<close>

lemma eq1_1:
  fixes k :: nat
  assumes "k > 0"
  shows "seqX (4*k-3) = seqX (2*k-1)"
  sorry

lemma eq1_2:
  fixes k :: nat
  assumes "k > 0"
  shows "-seqX (4*k-2) = seqX (2*k-1)"
  sorry

lemma eq2_1:
  fixes k :: nat
  assumes "k > 0"
  shows "seqX (4*k-1) = seqX (4*k)"
  sorry

lemma eq2_2:
  fixes k :: nat
  assumes "k > 0"
  shows "-seqX (2*k) = seqX (4*k)"
  sorry

lemma eq2_3:
  fixes k :: nat
  assumes "k > 0"
  shows "-seqX (2*k) = seqX (k)"
  sorry


\<comment>\<open> (2) \<close>
lemma S4k_eq_2Sk:
  fixes n :: nat
  assumes "n \<ge> 4" "n div 4 = 0"
  shows "sumFst n = 2 * sumFst (n div 2)"
  sorry

\<comment>\<open> (3) \<close>
lemma S4kp2_eq_S4k:
  fixes n :: nat
  assumes "n \<ge> 4" "n div 4 = 0"
  shows "sumFst (n+2) = sumFst n"
  sorry

\<comment>\<open> (4) \<close>
lemma Sn_eq_n_mod2:
  fixes n :: nat
  shows "(sumFst n) mod 2 = int (n mod 2)"
  sorry


\<comment> \<open> ===== Helpers ===== \<close>
(*
lemma sumFst_four:
  fixes i :: nat
  assumes "0 \<le> i" "i \<le> 4"
  shows "0 \<le> sumFst i"
  sorry
  
lemma Si_gt_0_4k:
  fixes k i :: nat
  assumes "k \<ge> 1"
  shows "\<forall>i \<le> 4*k. sumFst i \<ge> 0"
  using assms
proof(induction k rule: nat_induct_at_least)
  case base
  then show ?case
    using sumFst_four by simp
next
  case (Suc n)
  then show ?case sorry
qed
*)

\<comment> \<open> ===== Main problem ===== \<close>

lemma Si_gt_0:
  fixes i :: nat
  assumes "i \<ge> 1"
  shows "sumFst i \<ge> 0"
  using assms
  sorry
(*
proof (induction i rule: nat_induct_at_least)
  case base
  then show ?case by auto
next
  case (Suc n)
  then show ?case using Si_gt_0_4k 
    by (metis div_le_dividend le_Suc_eq nonzero_mult_div_cancel_left zero_neq_numeral)
qed
*)
end