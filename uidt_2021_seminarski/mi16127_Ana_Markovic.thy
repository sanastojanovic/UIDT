theory mi16127_Ana_Markovic
imports Complex_Main

begin

\<comment> 
\<open> https://www.imo-official.org/problems/IMO2010SL.pdf 
  Algebra A4
\<close>

(* definisanje oblika x_i *)
(* pomeranje indksa:
  x1 = 1
  x_2k = -x_k
    2k = n
    k = n / 2
  x_2k-1 = (-1)^(k+1)x_k
    2k-1 = n
    k = (n+1) / 2
*)
fun x_i_def :: "nat \<Rightarrow> int" where
"x_i_def n = ( if n = 0 then 0
               else if n = 1 then 1
               else if n mod 2 = 0 
                then (-1 * (x_i_def (n div 2))) 
               else 
                (-1)^((n + 1) div 2 + 1) * (x_i_def ((n + 1) div 2)))"

(* definisana suma x_i *)
primrec sum_of_x_i :: "nat \<Rightarrow> int" where
"sum_of_x_i 0 = 0" |
"sum_of_x_i (Suc n) = x_i_def (Suc n) + sum_of_x_i n"

(* definisane jednakosti 
   x_4k-3 = -x_4k-2 
   x_4k-1 = x_4k
*)
lemma equation_4k_3:
  shows "x_i_def (4*k-3) = (-1)*x_i_def (4*k-2)"
  sorry

lemma equation_4k_1:
  shows "x_i_def (4*k-1) = x_i_def (4*k)"
  sorry

(* definisane parcijalne sume *)
definition S_k :: "nat \<Rightarrow> int"where
"S_k n = (\<Sum>i\<le>n. (x_i_def i))"

definition S_4k :: "nat \<Rightarrow> int"where
"S_4k n = (\<Sum>i\<le>n. (
    (x_i_def (i*4-3) + x_i_def (i*4-2)) + 
    (x_i_def (i*4-1) + x_i_def (i*4))
  ))"

definition S_4k_2 :: "nat \<Rightarrow> int" where
"S_4k_2 n = (S_4k n 
             + x_i_def (4*n+1) 
             + x_i_def (4*n+2))"

definition S_4k_4 :: "nat \<Rightarrow> int" where
"S_4k_4 n = S_4k (n+1)"

definition S_4k_3 :: "nat \<Rightarrow> int" where
"S_4k_3 n = (S_4k_2 n + S_4k_4 n) div 2"

(* S_4k = 2*S_k *)
lemma S_4k_eq_2S_k:
  assumes "n\<ge>1"
  shows "S_4k n = 2 * S_k n"
  using assms
  sorry

(* S_4k+2 = S_4k *)
lemma S_4k_eq_S_4k_2:
  assumes "n\<ge>1"
  shows "S_4k_2 n = S_4k n"
  using assms
  sorry

(* Pokazivanje da su
   S_4k \<ge> 0
   S_4k+1 \<ge> 0
   S_4k+2 \<ge> 0
   S_4k+3 \<ge> 0
   S_4k+4 \<ge> 0 
   pod pretpostavkom da je S_k \<ge> 0
*)

lemma S_4k_nonegativ:
  assumes "n \<ge> 1"
  assumes "S_k n \<ge> 0"
  shows "S_4k n \<ge> 0"
  using assms
proof(induction n rule: nat_less_induct)
  case (1 n)
  then show ?case 
  proof-
    have "S_4k n = 2 * S_k n"
      using S_4k_eq_2S_k `n \<ge> 1` by simp
    also have "... \<ge> 0"
      using 1 by simp
    finally show ?case .
  qed 
qed

lemma S_4k_2_nonegativ:
  assumes "n \<ge> 1"
  assumes "S_k n \<ge> 0"
  shows "S_4k_2 n \<ge> 0"
  using assms
proof(induction n rule: nat_less_induct)
  case (1 n)
  then show ?case 
  proof-
    have "S_4k_2 n = S_4k n"
      using S_4k_eq_S_4k_2 `n \<ge> 1` by simp
    also have "... \<ge> 0"
      using 1 S_4k_nonegativ by simp
    finally show ?case .
  qed 
qed

lemma S_4k_4_nonegativ:
  assumes "n \<ge> 1"
  assumes "S_k (n+1) \<ge> 0"
  shows "S_4k_4 n \<ge> 0"
  using assms
proof(induction n rule: nat_less_induct)
  case (1 n)
  then show ?case 
  proof-
    have "S_4k_4 n = S_4k (n+1)"
      using S_4k_4_def by simp
    also have "... \<ge> 0"
      using 1 S_4k_nonegativ by simp
    finally show ?case .
  qed 
qed

lemma S_4k_3_nonegativ:
  assumes "n \<ge> 1"
  assumes "S_k n \<ge> 0"
  shows "S_4k_3 n \<ge> 0"
  using assms
proof(induction n rule: nat_less_induct)
  case (1 n)
  then show ?case sorry
qed

definition S_4k_1 :: "nat \<Rightarrow> int" where
"S_4k_1 n = S_4k n + x_i_def (4*n+1)"

definition S_4_k_1 :: "nat \<Rightarrow> int" where
"S_4_k_1 k = S_4k k + S_4k_1 k + S_4k_2 k + S_4k_3 k +  S_4k_4 k"

lemma S_4k_eq_S_4_k_1 :
  assumes "n\<ge>1"
  shows "S_4k n = S_4_k_1 (n-1)"
  sorry


lemma sum_k:
  fixes k::nat
  assumes "n \<le> (4*k)"
  assumes "n \<ge> 1"
  shows "S_4k n \<ge> 0"
  using assms
proof (induction n)
case 0
then show ?case by simp
next
  case (Suc n)
  then show ?case 
    sorry
qed


end