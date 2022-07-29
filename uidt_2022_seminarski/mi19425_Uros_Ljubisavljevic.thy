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

(*
fun seqX :: "nat \<Rightarrow> int" where
"seqX 0 = 0" |
"seqX n = ( case n = 1 of True \<Rightarrow> 1 |
            False \<Rightarrow> (case n mod 2 = 0 of True \<Rightarrow> (-seqX (n div 2)) | 
            False \<Rightarrow> ((-1)^((n + 3) div 2)) * (seqX ((n + 1) div 2))))"
*)

value "seqX "

\<comment>\<open> S_n definition \<close>
primrec sumFst :: "nat \<Rightarrow> int" where
"sumFst 0 = 0" |
"sumFst (Suc n) = seqX (Suc n) + sumFst n"

definition sumFstS :: "nat \<Rightarrow> int" where
"sumFstS n = (\<Sum>i::nat=0..n. seqX i)"

lemma sumFst_eq_sumFstS:
  fixes n :: nat
  shows "sumFst n = sumFstS n"
proof(induction n)
  case 0
  then show ?case using sumFstS_def by simp
next
  case (Suc n)
  then show ?case
  proof-
    have "sumFst (Suc n) = sumFst n + seqX (Suc n)" by simp
    also have "\<dots> = sumFstS n + seqX (Suc n)" using Suc by simp
    also have "\<dots> = sumFstS (Suc n)" using sumFstS_def by simp
    finally show ?thesis .
  qed
qed

value "sumFst 12"
value "sumFstS 0"

\<comment>\<open> ======== Observations: ======= \<close>
\<comment>\<open> (1) \<close>

lemma eq1_1:
  fixes k :: nat
  assumes "k \<ge> 1"
  shows "seqX (4*k-3) = seqX (2*k-1)"
proof-
  have "odd (4*k-3)" using assms by auto
  then have "seqX (4*k-3) = ((-1)^(((4*k-3) + 3) div 2)) * (seqX (((4*k-3) + 1) div 2))" using seqX.simps 
    by (metis (no_types, lifting) add_self_div_2 even_iff_mod_2_eq_zero even_zero minus_one_mult_self nat_1_add_1 neg_one_even_power numeral_Bit0 numeral_plus_numeral odd_even_add semiring_norm(4))
  also have "\<dots> = ((-1)^(2*k)) * (seqX ((2*k-1)))"
    by (smt (verit, del_insts) ab_semigroup_add_class.add_ac(1) add.commute add_diff_cancel_left' add_self_div_2 assms distrib_left_numeral less_eqE mult.commute mult.left_commute mult_2 nat_1_add_1 numeral_Bit0 numeral_Bit1)
  also have "\<dots> = seqX (2*k-1)" by simp
  finally show ?thesis .
qed

lemma eq1_2:
  fixes k :: nat
  assumes "k \<ge> 1"
  shows "-seqX (4*k-2) = seqX (2*k-1)"
proof-
  have "-seqX (4*k-2) = -seqX (2*(2*k-1))" using assms
    by (simp add: right_diff_distrib')
  also have "\<dots> = -(-seqX (2*k-1))" using seqX.simps by simp
  also have "\<dots> = seqX (2*k-1)" by simp
  finally show ?thesis .
qed

lemma eq1_2_1:
  fixes k :: nat
  assumes "k \<ge> 1"
  shows "-seqX (4*k-2) = seqX (4*k-3)" "seqX (4*k-2) = -seqX (4*k-3)"
  using eq1_1 eq1_2 assms apply simp
  by (smt (verit, del_insts) assms eq1_1 eq1_2)

lemma eq2_1:
  fixes k :: nat
  assumes "k \<ge> 1"
  shows "seqX (4*k-1) = seqX (4*k)"
proof-
  have "odd (4*k-1)" using assms by auto
  then have "seqX (4*k-1) = ((-1)^(((4*k-1) + 3) div 2)) * (seqX (((4*k-1) + 1) div 2))" using seqX.simps
    by (metis (no_types, lifting) add_self_div_2 even_iff_mod_2_eq_zero even_zero minus_one_mult_self nat_1_add_1 neg_one_even_power numeral_Bit0 numeral_plus_numeral odd_even_add semiring_norm(4))
  also have "\<dots> = ((-1)^((4*k + 2) div 2)) * (seqX ((4*k) div 2))" by simp
  also have "\<dots> = ((-1)^(2*k + 1)) * (seqX (2*k))" by simp
  also have "\<dots> = -seqX (2*k)" by simp
  also have "\<dots> = seqX (4*k)" by simp
  finally show ?thesis .
qed

lemma eq2_2:
  fixes k :: nat
  assumes "k > 0"
  shows "-seqX (2*k) = seqX (4*k)"
  by simp
  

lemma eq2_3:
  fixes k :: nat
  assumes "k > 0"
  shows "-seqX (2*k) = seqX (k)"
  by simp


\<comment>\<open> (2) \<close>

lemma S4k_eq_2Sk:
  fixes n k :: nat
  assumes "n = 4*k" "k \<ge> 1"
  shows "sumFst n = 2 * sumFst (n div 4)"
proof-
  have "sumFst n = (\<Sum>i::nat=1..n. seqX i)" using sumFst.simps
    by (simp add: sum.atLeast_Suc_atMost sumFstS_def sumFst_eq_sumFstS)
  also have "\<dots> = (\<Sum>i::nat=1..k. (seqX (4*i-3)) + (seqX (4*i-2)) + (seqX (4*i-1)) + (seqX (4*i)))" using assms sorry
  also have "\<dots> = (\<Sum>i::nat=1..k. (seqX (4*i-3)) + (-seqX (4*i-3)) + (seqX (4*i-1)) + (seqX (4*i)))" using eq1_2_1 assms by simp
  also have "\<dots> = (\<Sum>i::nat=1..k. (seqX (4*i-1)) + (seqX (4*i)))" by simp
  also have "\<dots> = (\<Sum>i::nat=1..k. (seqX (4*i)) + (seqX (4*i)))" using eq2_1 by simp
  also have "\<dots> = (\<Sum>i::nat=1..k. 2*(seqX i))" using eq2_2 eq2_3 by simp
  also have "\<dots> = 2 * (\<Sum>i::nat=1..k. (seqX i))" by (simp add: sum_distrib_left)
  also have "\<dots> = 2 * sumFst k" by (simp add: sum.atLeast_Suc_atMost sumFstS_def sumFst_eq_sumFstS)
  also with assms(1) have "\<dots> = 2 * sumFst (n div 4)" by simp
  finally show ?thesis .
qed


\<comment>\<open> (3) \<close>

lemma S4kp2_eq_S4k:
  fixes n k :: nat
  assumes "n = 4*k" "k \<ge> 1"
  shows "sumFst (n+2) = sumFst n"
proof-
  have "sumFst (n+2) = sumFst n + seqX (4*k+1) + seqX (4*k+2)" using assms by simp
  also have "\<dots> = sumFst n + seqX (4*(k+1)-3) + seqX (4*(k+1)-2)" by simp
  also have "\<dots> = sumFst n + seqX (4*(k+1)-3) + (-seqX (4*(k+1)-3))" using eq1_2_1 le_add2 by presburger
  also have "\<dots> = sumFst n" by simp
  finally show ?thesis .
qed

\<comment>\<open> (4) \<close>

(* helper *)
lemma seqXimage:
  fixes n :: nat
  assumes "n \<ge> 1"
  shows "(seqX n = -1) \<or> (seqX n = 1)"
  sorry  

lemma Sn_eq_n_mod2:
  fixes n :: nat
  assumes "n \<ge> 1"
  shows "(sumFst n) mod 2 = int (n mod 2)"
  using assms
proof(induction n rule: nat_induct_at_least)
  case base
  then show ?case by simp
next
  case (Suc n)
  then show ?case
  proof-
    have "sumFst (Suc n) mod 2 = (sumFst n + seqX (Suc n)) mod 2" unfolding sumFst_def
      by (metis add.commute old.nat.simps(7))
    also have "\<dots> = ((sumFst n) mod 2 + (seqX (Suc n)) mod 2) mod 2"
      by (metis mod_add_eq)
    also have "\<dots> = (int (n mod 2) + (seqX (Suc n)) mod 2) mod 2" using Suc
      by presburger
    also have "\<dots> = (int (n mod 2) + 1) mod 2" using seqXimage
      by (metis Suc.hyps le_SucI minus_1_mod_2_eq one_mod_two_eq_one)
    also have "\<dots> = int (Suc n mod 2) mod 2"
      by (metis Suc_eq_plus1_left bits_mod_0 int_Suc mod_Suc mod_self of_nat_0 of_nat_eq_1_iff one_add_one)
    also have "\<dots> = int (Suc n mod 2)" by simp
    finally show ?thesis .
  qed
qed


\<comment> \<open> ===== Helpers ===== \<close>

lemma sgnPowEven:
  assumes "even n"
  shows "(-1)^n = 1"
  using assms
proof
  fix k :: nat
  assume "n = 2 * k"
  then have "(-1)^n = (-1)^(2*k)" by simp
  also have "\<dots> = 1" using power_minus1_even[of k] sorry
  finally show ?thesis .
qed

lemma sumFst_four:
  assumes "i \<le> 4"
  shows "0 \<le> sumFst i"
proof-
  have "\<forall>i \<le> 0. sumFst i \<ge> 0" by simp
  
  have "sumFst 1 \<ge> 0" by simp
  with \<open>\<forall>i \<le> 0. sumFst i \<ge> 0\<close> have "\<forall>i \<le> 1. sumFst i \<ge> 0"
    by (metis less_one nat_less_le verit_comp_simplify1(3))
  
  have "sumFst 2 \<ge> 0" unfolding sumFst_def by simp
  with \<open>\<forall>i \<le> 1. sumFst i \<ge> 0\<close> have "\<forall>i \<le> 2. sumFst i \<ge> 0"
    by (metis Suc_1 le_SucE)
  
  have "sumFst 3 \<ge> 0" unfolding sumFst_def by simp
  with \<open>\<forall>i \<le> 2. sumFst i \<ge> 0\<close> have "\<forall>i \<le> 3. sumFst i \<ge> 0"
    by (metis eval_nat_numeral(3) le_Suc_eq)

  have "sumFst 4 \<ge> 0" unfolding sumFst_def by simp
  with \<open>\<forall>i \<le> 3. 0 \<le> sumFst i\<close> assms show ?thesis using sumFst.simps
    by (metis Suc_numeral le_SucE semiring_norm(2) semiring_norm(8))
qed

lemma Si_gt_0_4k:
  fixes k :: nat
  assumes "1 \<le> k" "i \<le> 4*k"
  shows "0 \<le> sumFst i"
  using assms
proof(induction k rule: nat_induct_at_least)
  case base
  then show ?case using sumFst_four by simp
next
  case (Suc n)
  then show ?case
  proof-
    have 1: "((i \<le> 4 * Suc n) \<longrightarrow> (0 \<le> sumFst i)) \<longleftrightarrow> 
          (((i \<le> 4*n) \<longrightarrow> (0 \<le> sumFst i)) \<and> 
          ((i = 4*n+1) \<longrightarrow> (0 \<le> sumFst i)) \<and> 
          ((i = 4*n+2) \<longrightarrow> (0 \<le> sumFst i)) \<and> 
          ((i = 4*n+3) \<longrightarrow> (0 \<le> sumFst i)) \<and>
          ((i = 4*n+4) \<longrightarrow> (0 \<le> sumFst i)))"
    proof
      assume "(i \<le> 4 * Suc n) \<longrightarrow> (0 \<le> sumFst i)"
      then have "(i \<le> 4 * n + 4) \<longrightarrow> (0 \<le> sumFst i)" by simp
      then show "((i \<le> 4*n) \<longrightarrow> (0 \<le> sumFst i)) \<and> 
          ((i = 4*n+1) \<longrightarrow> (0 \<le> sumFst i)) \<and> 
          ((i = 4*n+2) \<longrightarrow> (0 \<le> sumFst i)) \<and> 
          ((i = 4*n+3) \<longrightarrow> (0 \<le> sumFst i)) \<and>
          ((i = 4*n+4) \<longrightarrow> (0 \<le> sumFst i))" by linarith
    next
      assume "(i \<le> 4 * n \<longrightarrow> 0 \<le> sumFst i) \<and>
              (i = 4 * n + 1 \<longrightarrow> 0 \<le> sumFst i) \<and> 
              (i = 4 * n + 2 \<longrightarrow> 0 \<le> sumFst i) \<and> 
              (i = 4 * n + 3 \<longrightarrow> 0 \<le> sumFst i) \<and>
              (i = 4 * n + 4 \<longrightarrow> 0 \<le> sumFst i)"
      then have "((i \<le> 4 * n + 3) \<longrightarrow> (0 \<le> sumFst i)) \<and> (i = 4 * n + 4 \<longrightarrow> 0 \<le> sumFst i)"
        by (metis add.right_neutral add_Suc_right le_SucE numeral_1_eq_Suc_0 numeral_2_eq_2 numeral_3_eq_3 numerals(1))
      then show "(i \<le> 4 * Suc n) \<longrightarrow> (0 \<le> sumFst i)" by force
    qed

    have 10: "(i \<le> 4*n) \<longrightarrow> (0 \<le> sumFst i)" using Suc(2) by simp

    have 14: "i = 4 * n + 4 \<longrightarrow> 0 \<le> sumFst i"
    proof
      assume "i = 4*n + 4"
      then have "(i div 4) \<le> 4*n" using Suc by simp
      with Suc(1) \<open>i = 4*n + 4\<close> have "i mod 4 = 0" "4 \<le> i" by auto
      then have "sumFst i = 2*(sumFst (i div 4))" using S4k_eq_2Sk[of i]
        by (metis Suc_eq_plus1 \<open>i = 4 * n + 4\<close> add.commute le_add2 mult.commute mult_Suc)
      from \<open>(i div 4) \<le> 4*n\<close> have "(sumFst (i div 4)) \<ge> 0" using Suc(2) sorry
      with \<open>sumFst i = 2*(sumFst (i div 4))\<close> show "sumFst i \<ge> 0" by simp
    qed
   
    have 13: "i = 4 * n + 3 \<longrightarrow> 0 \<le> sumFst i"
    proof
      assume "i = 4*n + 3"
      then have "sumFst i = sumFst (4*n + 2) + seqX (4*n + 3)" by (simp add: numeral_3_eq_3)
      also with \<open>1 \<le> n\<close> have "\<dots> = sumFst (4*n) + seqX (4*n + 3)" using S4kp2_eq_S4k
        by simp
      also have "\<dots> = sumFst (4*n) + seqX (4*(n+1) - 1)" by (simp add: algebra_simps)
      also have "\<dots> = sumFst (4*n) + seqX (n + 1)" using eq2_1 eq2_2 eq2_3
        by (metis add_gr_0 le_add2 less_numeral_extra(1))
      also have "\<dots> = 2 * sumFst n + seqX (n + 1)" using S4k_eq_2Sk using Suc(1) by auto
      also have "\<dots> = 2 * sumFst n + sumFst (n + 1) - sumFst n" by simp
      also have "\<dots> = sumFst n + sumFst (n + 1)" by simp
      also have "\<dots> \<ge> 0"
      proof-
        (* ? ? ? ? ? *)
        have "(n+1) \<le> 4*n" using Suc(1) by simp
        have "n \<le> 4*n" by simp
        then have "sumFst n \<ge> 0" using Suc sorry
        moreover with \<open>(n+1) \<le> 4*n\<close> have "sumFst (n+1) \<ge> 0" using Suc sorry
        ultimately show ?thesis by linarith
      qed
      finally show ?case .
    qed

    have 12: "i = 4 * n + 2 \<longrightarrow> 0 \<le> sumFst i"
    proof
      assume "i = 4*n + 2"
      then have "sumFst i = sumFst (4*n)" using S4kp2_eq_S4k[of i]
        using S4kp2_eq_S4k Suc(1) by simp
      also have "\<dots> \<ge> 0" using Suc sorry
      finally show ?case .
    qed

    have 11: "i = 4 * n + 1 \<longrightarrow> 0 \<le> sumFst i"   
    proof(cases "n mod 2 = 0")
      case True
      then show ?thesis
      proof-
  
        assume "n mod 2 = 0"
        then have "((-1)^((2*(n + 1) + 2) div 2)) = 1"
        proof-
          have "even ((2*(n + 1) + 2) div 2)" using True by fastforce
          then show "(-1)^((2*(n + 1) + 2) div 2) = 1" using sgnPowEven[where n = "((2*(n + 1) + 2) div 2)"] by simp
        qed

        have "seqX (4 * n + 1) = seqX (n + 1)"
        proof-
          from \<open>n mod 2 = 0\<close> have "(n+1) mod 2 = 1" by auto
          then have "(2*(n+1) -1) mod 2 = 1" by auto
          have "seqX (4*n + 1) = seqX (4*(n+1) - 3)" by (simp add: algebra_simps)
          also have "\<dots> = seqX (2*(n+1) - 1)" using eq1_1[where k = "n+1"] by simp
          also with \<open>(2*(n+1) -1) mod 2 = 1\<close> have "\<dots> = ((-1)^((2*(n+1) - 1 + 3) div 2)) * (seqX ((2*(n+1) - 1 + 1) div 2))" 
            by (metis Nat.le_imp_diff_is_add Suc.hyps bits_mod_0 calculation diff_add_inverse2 diff_le_self diff_self_eq_0 mult_eq_self_implies_10 not_numeral_le_zero numeral_Bit0 numeral_One seqX.elims zero_neq_numeral)
          also have "\<dots> = ((-1)^((2*(n + 1) + 2) div 2)) * (seqX ((2*n+2) div 2))" by (simp add: algebra_simps)
          also with \<open>((-1)^((2*(n + 1) + 2) div 2)) = 1\<close> have "\<dots> = (seqX ((2*n+2) div 2))"
            by (smt (verit) left_minus_one_mult_self power_add_numeral2 power_one)
          also have "\<dots> = seqX (n+1)" by simp
          finally show ?thesis .
        qed        

        show "i = 4 * n + 1 \<longrightarrow> 0 \<le> sumFst i"
        proof
          assume "i = 4*n + 1"
          then have "sumFst i = sumFst (4*n) + seqX (4*n + 1)" by simp
          also with \<open>seqX (4 * n + 1) = seqX (n + 1)\<close> have "\<dots> = sumFst (4*n) + seqX (n + 1)" by simp
          also have "\<dots> = 2*sumFst n + seqX (n + 1)" using S4k_eq_2Sk Suc(1) by simp
          also have "\<dots> = 2*sumFst n + sumFst (n + 1) - sumFst n" by simp
          also have "\<dots> = sumFst n + sumFst (n + 1)" by simp
          also have "\<dots> \<ge> 0" using Suc sorry
          finally show "sumFst i \<ge> 0" .
        qed
      qed
    next
      case False
      then show ?thesis
      proof-
        assume "n mod 2 \<noteq> 0"
        show "i = 4 * n + 1 \<longrightarrow> 0 \<le> sumFst i"
        proof
          have "(sumFst n) mod 2 = 1" using Sn_eq_n_mod2
            using False by auto
          then have "sumFst n \<ge> 1" sorry

          have "sumFst(4*n) = 2*sumFst(n)" using S4k_eq_2Sk Suc(1) by simp
          also with \<open>sumFst n \<ge> 1\<close> have "\<dots> \<ge> 2" by simp 
          finally have "sumFst (4*n) \<ge> 2" .

          assume "i = 4*n +1"
          then have "sumFst i = sumFst (4*n) + seqX (4*n + 1)" by simp
          also with \<open>sumFst (4*n) \<ge> 2\<close> have "\<dots> \<ge> 0" using seqXimage
            by (smt (verit, del_insts) le_add_same_cancel2 zero_le)
          finally show "sumFst i \<ge> 0" .
        qed
      qed
    qed

    show ?case using 1 10 11 12 13 14
      using Suc.prems by blast
  qed
qed

\<comment> \<open> ===== Main problem ===== \<close>

lemma Si_gt_0:
  fixes i :: nat
  assumes "i \<ge> 1"
  shows "sumFst i \<ge> 0"
  using assms Si_gt_0_4k by simp

end