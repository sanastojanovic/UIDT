theory mi19425_Uros_Ljubisavljevic
  imports Main
begin

text\<open>https://www.imo-official.org/problems/IMO2010SL.pdf\<close>

\<comment>\<open> Sequence definiton \<close>
(*
fun seqX :: "nat \<Rightarrow> int" where
"seqX 0 = 0" |
"seqX n = ( if (n = 1) then 1
            else if (n mod 2 = 0) then (-seqX (n div 2))
            else ((-1)^((n + 3) div 2)) * (seqX ((n + 1) div 2)))"
*)

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
  assumes "n mod 4 = 0"
  shows "sumFst n = 2 * sumFst (n div 4)"
  sorry

\<comment>\<open> (3) \<close>
lemma S4kp2_eq_S4k:
  fixes n :: nat
  assumes "n mod 4 = 0"
  shows "sumFst (n+2) = sumFst n"
  sorry

\<comment>\<open> (4) \<close>
lemma Sn_eq_n_mod2:
  fixes n :: nat
  shows "(sumFst n) mod 2 = int (n mod 2)"
  sorry


\<comment> \<open> ===== Helpers ===== \<close>

lemma seqXabs1:
  fixes n :: nat
  shows "(seqX n \<ge> -1) \<and> (seqX n \<le> 1)"
  using seqX.simps
  sorry

lemma sgnPowEven:
  assumes "even n"
  shows "(-1)^n = 1"
  sorry  

lemma sumFst_four:
  fixes i :: nat
  assumes "i \<le> 4"
  shows "\<forall>i\<le>4. 0 \<le> sumFst i"
  using assms
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
  with \<open>\<forall>i \<le> 3. 0 \<le> sumFst i\<close> show ?thesis
    sorry
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
      then have "sumFst i = 2*(sumFst (i div 4))" using S4k_eq_2Sk[of i] by simp
      from \<open>(i div 4) \<le> 4*n\<close> have "(sumFst (i div 4)) \<ge> 0" using Suc(2) sorry
      with \<open>sumFst i = 2*(sumFst (i div 4))\<close> show "sumFst i \<ge> 0" by simp
    qed
   
    have 13: "i = 4 * n + 3 \<longrightarrow> 0 \<le> sumFst i"
    proof
      assume "i = 4*n + 3"
      then have "sumFst i = sumFst (4*n + 2) + seqX (4*n + 3)" by (simp add: numeral_3_eq_3)
      also with \<open>1 \<le> n\<close> have "\<dots> = sumFst (4*n) + seqX (4*n + 3)" using S4kp2_eq_S4k
        by (metis mod_mult_self1_is_0)
      also have "\<dots> = sumFst (4*n) + seqX (4*(n+1) - 1)" by (simp add: algebra_simps)
      also have "\<dots> = sumFst (4*n) + seqX (n + 1)" using eq2_1 eq2_2 eq2_3
        by (metis add_gr_0 less_numeral_extra(1))
      also have "\<dots> = 2 * sumFst n + seqX (n + 1)" by (simp add: S4k_eq_2Sk)
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
        by (meson S4kp2_eq_S4k mod_mult_self1_is_0)
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
          also have "\<dots> = 2*sumFst n + seqX (n + 1)" using S4k_eq_2Sk by simp
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

          have "sumFst(4*n) = 2*sumFst(n)" using S4k_eq_2Sk by simp
          also with \<open>sumFst n \<ge> 1\<close> have "\<dots> \<ge> 2" by simp 
          finally have "sumFst (4*n) \<ge> 2" .

          assume "i = 4*n +1"
          then have "sumFst i = sumFst (4*n) + seqX (4*n + 1)" by simp
          also with \<open>sumFst (4*n) \<ge> 2\<close> have "\<dots> \<ge> 0" using seqXabs1
            by (smt (verit))
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