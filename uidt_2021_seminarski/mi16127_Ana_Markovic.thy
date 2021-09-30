theory mi16127_Ana_Markovic
imports Complex_Main

begin

\<comment> 
\<open> https://www.imo-official.org/problems/IMO2010SL.pdf 
  Algebra A4
\<close>

fun x_i_def :: "nat \<Rightarrow> int" where
"x_i_def n = ( if n = 0 then 0
               else if n = 1 then 1
               else if n mod 2 = 0 
                then (-1 * (x_i_def (n div 2))) 
               else 
                (-1)^((n + 1) div 2 + 1) * (x_i_def ((n + 1) div 2)))"

primrec sum_of_x_i :: "nat \<Rightarrow> int" where
"sum_of_x_i 0 = 0" |
"sum_of_x_i (Suc n) = x_i_def (Suc n) + sum_of_x_i n"

lemma equation_4k_3:
  shows "x_i_def (4*k-3) = (-1)*x_i_def (4*k-2)"
  sorry

lemma equation_4k_1:
  shows "x_i_def (4*k-1) = x_i_def (4*k)"
  sorry

(* S_4k \<Rightarrow> 4k = n*)
definition S_4k :: "nat \<Rightarrow> int"where
"S_4k n = (\<Sum>i\<le>n. (
    (x_i_def (i*4-3) + x_i_def (i*4-2)) + 
    (x_i_def (i*4-1) + x_i_def (i*4))
  ))"

definition S_4k_2 :: "nat \<Rightarrow> int"where
"S_4k_2 n = (S_4k n 
             + x_i_def (4*n+1) 
             + x_i_def (4*n+2))"

value "S_4k_2 10"

definition S_k :: "nat \<Rightarrow> int"where
"S_k n = (\<Sum>i\<le>n. (x_i_def i))"

lemma S_4k_eq_2S_k:
  assumes "n\<ge>4"
  assumes "n mod 4 = 0"
  shows "2 * S_k n = S_4k n"
  using assms
  sorry

lemma S_4k_eq_S_4k_2:
  assumes "n\<ge>6"
  shows "S_4k_2 n = S_4k n"
  using assms
  sorry

lemma S_4k_nonegativ:
  assumes "n \<ge> 1"
  shows "S_4k n \<ge> 0"
  using assms
proof(induction n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then show ?case 
  proof -
    have "S_4k (Suc n) =  (\<Sum>i\<le>(Suc n). (
    (x_i_def (i*4-3) + x_i_def (i*4-2)) + 
    (x_i_def (i*4-1) + x_i_def (i*4))
    ))"
      using S_4k_def by simp
    also have "... = (\<Sum>i\<le>(Suc n). (0 + 
    (x_i_def (i*4-1) + x_i_def (i*4))))"
      using equation_4k_3 by (simp add: algebra_simps)
    also have "... = (\<Sum>i\<le>(Suc n). (x_i_def (i*4) + x_i_def (i*4)))"
      using equation_4k_1 by (simp add: algebra_simps)
    also have "... = (\<Sum>i\<le>(Suc n). (2*x_i_def (i*4)))"
       by (smt (verit, del_insts) sum.cong)
     also have "... = 2*(\<Sum>i\<le>(Suc n). (x_i_def (i*4)))"
       sorry   
     finally show ?case sorry
   qed
 qed

lemma sum_k:
  fixes k::nat
  assumes "n \<le> (4*k)"
  shows "S_k n \<ge> 0"
  using assms
proof (induction n rule: nat_less_induct)
  case (1 n)
  thm 1
  then show ?case 
    sorry
qed

lemma sum:
  fixes n::nat
  assumes "n > 0"
  shows "(sum_of_x_i n) \<ge> 0"
proof (induction n)
case 0
  then show ?case by simp
next
  case (Suc n)
  then show ?case sorry
qed

end
